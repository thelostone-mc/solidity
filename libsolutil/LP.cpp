/*
	This file is part of solidity.

	solidity is free software: you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation, either version 3 of the License, or
	(at your option) any later version.

	solidity is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with solidity.  If not, see <http://www.gnu.org/licenses/>.
*/
// SPDX-License-Identifier: GPL-3.0

#include <libsolutil/LP.h>

#include <libsolutil/CommonData.h>
#include <liblangutil/Exceptions.h>

using namespace std;
using namespace solidity;
using namespace solidity::util;
using namespace solidity::smtutil;

using rational = boost::rational<bigint>;


namespace
{

string toString(rational const& _value)
{
	if (_value.denominator() == bigint(1))
		return _value.numerator().str();
	else
		return to_string(_value);
}

vector<rational>& operator/=(vector<rational>& _data, rational const& _divisor)
{
	for (rational& x: _data)
		x /= _divisor;
	return _data;
}

vector<rational>& operator*=(vector<rational>& _data, rational const& _factor)
{
	for (rational& x: _data)
		x *= _factor;
	return _data;
}

vector<rational> operator-(vector<rational> const& _x, vector<rational> const& _y)
{
	vector<rational> result = vector<rational>(max(_x.size(), _y.size()), rational{});
	for (size_t i = 0; i < result.size(); ++i)
	{
		result[i] = i < _x.size() ? _x.at(i) : 0;
		result[i] -= i < _y.size() ? _y.at(i) : 0;
	}
	return result;
}

vector<rational> add(vector<rational> const& _x, vector<rational> const& _y)
{
	vector<rational> result = vector<rational>(max(_x.size(), _y.size()), rational{});
	for (size_t i = 0; i < result.size(); ++i)
	{
		result[i] = i < _x.size() ? _x.at(i) : 0;
		result[i] += i < _y.size() ? _y.at(i) : 0;
	}
	return result;
}

bool isConstant(vector<rational> const& _x)
{
	for (size_t i = 1; i < _x.size(); ++i)
		if (_x.at(i) != 0)
			return false;
	return true;
}

/// Multiply two vectors where the first element of each vector is a constant factor.
/// Only works if at most one of the vector has a nonzero element after the first.
vector<rational> vectorProduct(vector<rational> _x, vector<rational> _y)
{
	if (!isConstant(_y))
		swap(_x, _y);
	solAssert(isConstant(_y), "");

	rational factor = _y.front();

	for (rational& element: _x)
		element *= factor;
	return _x;
}


/**
 * Simplex tableau with the first row representing the objective function.
 */
struct Tableau
{
	std::vector<std::vector<rational>> data;
};


/// Add slack variables to turn the tableau into equational form.
Tableau toEquationalForm(Tableau _tableau)
{
	size_t rows = _tableau.data.size();
	size_t columns = _tableau.data.at(0).size();
	for (size_t i = 0; i < rows; ++i)
	{
		solAssert(_tableau.data[i].size() == columns, "");
		_tableau.data[i] += vector<bigint>(rows - 1, bigint{});
		if (i != 0)
			_tableau.data[i][columns + i - 1] = 1;
	}

	return _tableau;
}

optional<size_t> findPivotColumn(Tableau const& _tableau)
{
	size_t column = 1;
	rational maxValue = _tableau.data[0][column];
	for (size_t i = 2; i < _tableau.data[0].size(); ++i)
		if (_tableau.data[0][i] > maxValue)
		{
			maxValue = _tableau.data[0][i];
			column = i;
		}

	if (maxValue <= rational{0})
		return nullopt; // found optimum
	else
		return column;
}

optional<size_t> findPivotRow(Tableau const& _tableau, size_t _pivotColumn)
{
	size_t row = 0;
	optional<rational> minRatio;
	for (size_t i = 1; i < _tableau.data.size(); ++i)
	{
		if (_tableau.data[i][_pivotColumn] == 0)
			continue;
		rational ratio = _tableau.data[i][0] / _tableau.data[i][_pivotColumn];
		if (0 < ratio && (!minRatio || ratio < *minRatio))
		{
			minRatio = ratio;
			row = i;
		}
	}

	if (!minRatio)
		return nullopt; // unbounded
	else
		return row;
}

Tableau performPivot(Tableau _tableau, size_t _pivotRow, size_t _pivotColumn)
{
	rational pivot = _tableau.data[_pivotRow][_pivotColumn];
	solAssert(pivot != 0, "");
	_tableau.data[_pivotRow] /= pivot;
	solAssert(_tableau.data[_pivotRow][_pivotColumn] == rational(1), "");

	for (size_t i = 0; i < _tableau.data.size(); ++i)
		if (i != _pivotRow)
		{
			rational multiplier = _tableau.data[i][_pivotColumn];
			for (size_t j = 0; j < _tableau.data.front().size(); ++j)
				_tableau.data[i][j] -= multiplier * _tableau.data[_pivotRow][j];
		}
	return _tableau;
}

void printVector(vector<rational> const& _v)
{
	for (auto const& element: _v)
		cout << toString(element) << ", ";
	cout << endl;
}

void printTableau(Tableau _tableau)
{
	cout << "------------" << endl;
	for (auto const& row: _tableau.data)
		printVector(row);
	cout << "------------" << endl;
}

Tableau selectLastVectorsAsBasis(Tableau _tableau)
{
	// We might skip the operation for a column if it is already the correct
	// unit vector and its cost coefficient is zero.
	size_t columns = _tableau.data.at(0).size();
	size_t rows = _tableau.data.size();
	for (size_t i = 1; i < rows; ++i)
		_tableau = performPivot(move(_tableau), i, columns - rows + i);

	return _tableau;
}

/// Returns the row containing 1 if all other rows are zero.
optional<size_t> basisVariable(Tableau const& _tableau, size_t _column)
{
	optional<size_t> row;
	for (size_t i = 1; i < _tableau.data.size(); ++i)
		if (_tableau.data[i][_column] == bigint(1))
		{
			if (row)
				return {};
			else
				row = i;
		}
		else if (_tableau.data[i][_column] != 0)
			return {};
	return row;
}

vector<rational> optimalVector(Tableau const& _tableau)
{
	vector<rational> result;
	set<size_t> rowsSeen;
	for (size_t j = 1; j < _tableau.data[0].size(); j++)
	{
		optional<size_t> row = basisVariable(_tableau, j);
		if (row && rowsSeen.count(*row))
			row = nullopt;
		result.emplace_back(row ? _tableau.data[*row][0] : rational{});
		if (row)
			rowsSeen.insert(*row);
	}
	solAssert(rowsSeen.size() == _tableau.data.size() - 1, "");
	return result;
}

enum class LPResult
{
	Unknown,
	Unbounded,
	Feasible,
	Infeasible
};

/// Solve the LP Ax = b s.t. min c^Tx
/// The first row encodes the objective function
/// The first column encodes b
/// Assumes the tableau has a trivial basic feasible solution.
pair<LPResult, vector<rational>> simplexEq(Tableau _tableau)
{
	size_t iterations = 50 + _tableau.data[0].size() * 4;
	for (size_t step = 0; step <= iterations; ++step)
	{
		optional<size_t> pivotColumn = findPivotColumn(_tableau);
		if (!pivotColumn)
		{
			cout << "Optimum: ";
			vector<rational> optimum = optimalVector(_tableau);
			printVector(optimum);

			return make_pair(LPResult::Feasible, move(optimum));
		}
		cout << "Pivot column: " << *pivotColumn << endl;
		optional<size_t> pivotRow = findPivotRow(_tableau, *pivotColumn);
		if (!pivotRow)
		{
			cout << "unbounded" << endl;
			return make_pair(LPResult::Unbounded, optimalVector(_tableau));
		}
		cout << "Pivot row: " << *pivotRow << endl;
		_tableau = performPivot(move(_tableau), *pivotRow, *pivotColumn);
		cout << "After step " << step << endl;
		printTableau(_tableau);
	}
	return make_pair(LPResult::Unknown, vector<rational>{});
}

pair<LPResult, Tableau> simplexPhaseI(Tableau _tableau)
{
	vector<rational> originalObjective = _tableau.data[0];

	size_t rows = _tableau.data.size();
	size_t columns = _tableau.data.at(0).size();
	for (size_t i = 1; i < rows; ++i)
	{
		if (_tableau.data[i][0] < 0)
			_tableau.data[i] *= -1;
		_tableau.data[i] += vector<bigint>(rows - 1, bigint{});
		_tableau.data[i][columns + i - 1] = 1;
	}
	_tableau.data[0] =
		vector<rational>(columns, rational{}) +
		vector<rational>(rows - 1, rational{-1});

	cout << "Phase I tableau: " << endl;
	printTableau(_tableau);

	_tableau = selectLastVectorsAsBasis(move(_tableau));

	cout << "After basis selection: " << endl;
	printTableau(_tableau);

	LPResult result;
	vector<rational> optimum;
	tie(result, optimum) = simplexEq(_tableau);

	// TODO Can it be unbounded?
	if (result != LPResult::Feasible)
		return make_pair(LPResult::Unknown, Tableau{});

	for (size_t i = columns; i < optimum.size(); ++i)
		if (optimum[i] != 0)
			return make_pair(LPResult::Infeasible, Tableau{});

	_tableau.data[0] = originalObjective;
	for (size_t i = 1; i < rows; ++i)
		_tableau.data[i].resize(columns);

	cout << "Tableau after Phase I: " << endl;
	printTableau(_tableau);

	_tableau = selectLastVectorsAsBasis(move(_tableau));
	cout << "After basis correction: " << endl;
	printTableau(_tableau);

	return make_pair(LPResult::Feasible, move(_tableau));
}

bool needsPhaseI(Tableau const& _tableau)
{
	for (size_t i = 1; i < _tableau.data.size(); ++i)
		if (_tableau.data[i][0] < 0)
			return true;
	return false;
}

/// Solve the LP Ax <= b s.t. min c^Tx
/// The first row encodes the objective function
/// The first column encodes b
pair<LPResult, vector<rational>> simplex(Tableau _tableau)
{
	printTableau(_tableau);
	_tableau = toEquationalForm(move(_tableau));
	cout << "Equational: " << endl;
	printTableau(_tableau);
	if (needsPhaseI(_tableau))
	{
		LPResult result;
		tie(result, _tableau) = simplexPhaseI(_tableau);
		if (result == LPResult::Infeasible || result == LPResult::Unknown)
			return make_pair(result, vector<rational>{});
		solAssert(result == LPResult::Feasible, "");
	}
	return simplexEq(_tableau);
}

}

void LPSolver::reset()
{
	m_state = stack<State>{{State{}}};
}

void LPSolver::push()
{
	m_state.push(m_state.top());
}

void LPSolver::pop()
{
	m_state.pop();
	solAssert(!m_state.empty(), "");
}

void LPSolver::declareVariable(string const& _name, SortPointer const& _sort)
{
	solAssert(_sort && _sort->kind == Kind::Int, "");
	solAssert(!m_state.top().variables.count(_name), "");
	size_t index = m_state.top().variables.size() + 1;
	m_state.top().variables[_name] = index;
}

void LPSolver::addAssertion(Expression const& _expr)
{
	if (_expr.name == "and")
	{
		addAssertion(_expr.arguments.at(0));
		addAssertion(_expr.arguments.at(1));
	}
	else if (_expr.name == "<=")
	{
		vector<rational> constraint =
			parseLinearSum(_expr.arguments.at(0)) -
			parseLinearSum(_expr.arguments.at(1));
		constraint[0] *= -1;
		m_state.top().constraints.emplace_back(move(constraint));
	}
	else if (_expr.name == ">=")
		addAssertion(_expr.arguments.at(1) <= _expr.arguments.at(0));
	else if (_expr.name == "=")
	{
		addAssertion(_expr.arguments.at(0) <= _expr.arguments.at(1));
		addAssertion(_expr.arguments.at(1) <= _expr.arguments.at(0));
	}
	else
		solAssert(false, "Invalid operation: " + _expr.name);

}

pair<CheckResult, vector<string>> LPSolver::check(vector<Expression> const& _expressionsToEvaluate)
{
	vector<vector<rational>> constraints = m_state.top().constraints;
	size_t numColumns = 0;
	for (auto const& row: constraints)
		numColumns = max(numColumns, row.size());
	for (auto& row: constraints)
		row.resize(numColumns);

	Tableau tableau;
	tableau.data.push_back(vector<rational>(1, rational(bigint(0))) + vector<rational>(numColumns - 1, rational(bigint(1))));
	tableau.data += move(constraints);
	CheckResult smtResult;
	LPResult lpResult;
	vector<rational> solution;
	tie(lpResult, solution) = simplex(tableau);
	switch (lpResult)
	{
	case LPResult::Feasible:
	case LPResult::Unbounded: // TODO true?
		smtResult = CheckResult::SATISFIABLE;
		break;
	case LPResult::Infeasible:
		return make_pair(CheckResult::UNSATISFIABLE, vector<string>{});
	case LPResult::Unknown:
		return make_pair(CheckResult::UNKNOWN, vector<string>{});
		break;
	}

	vector<string> model;
	for (Expression const& e: _expressionsToEvaluate)
	{
		if (e.arguments.empty() && m_state.top().variables.count(e.name))
		{
			size_t index = m_state.top().variables.at(e.name);
			solAssert(index > 0, "");
			model.emplace_back(toString(solution.at(index - 1)));
		}
		else
		{
			model = {};
			break;
		}
	}
	return make_pair(smtResult, move(model));
}

vector<rational> LPSolver::parseLinearSum(smtutil::Expression const& _expr) const
{
	if (_expr.arguments.empty() || _expr.name == "*")
		return parseProduct(_expr);
	else if (_expr.name == "+")
		return add(parseLinearSum(_expr.arguments.at(0)), parseLinearSum(_expr.arguments.at(1)));
	else if (_expr.name == "-")
		return parseLinearSum(_expr.arguments.at(0)) - parseLinearSum(_expr.arguments.at(1));
	else
		solAssert(false, "");
}

vector<rational> LPSolver::parseProduct(smtutil::Expression const& _expr) const
{
	vector<rational> result;
	if (_expr.arguments.empty())
		return parseFactor(_expr);
	else if (_expr.name == "*")
		// The multiplication ensures that only one of them can be a variable.
		return vectorProduct(parseFactor(_expr.arguments.at(0)), parseFactor(_expr.arguments.at(1)));
	else
		solAssert(false, "");

	return result;
}

vector<rational> LPSolver::parseFactor(smtutil::Expression const& _expr) const
{
	solAssert(_expr.arguments.empty(), "");
	solAssert(!_expr.name.empty(), "");
	if ('0' <= _expr.name[0] && _expr.name[0] <= '9')
		return {rational(bigint(_expr.name))};
	else if (_expr.name == "true")
		return {rational(bigint(1))};
	else if (_expr.name == "false")
		return {rational(bigint(0))};

	size_t index = m_state.top().variables.at(_expr.name);
	solAssert(index > 0, "");
	vector<rational> result(index + 1);
	result[index] = rational(bigint(1));
	return result;
}
