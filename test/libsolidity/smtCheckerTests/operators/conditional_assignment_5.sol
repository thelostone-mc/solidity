pragma experimental SMTChecker;

abstract contract D {
    function d() public virtual ;
}

contract C {
    bool a;
    uint x;
    D d;
    function g() public returns (uint) {
        x = 2;
        d.d();
        return x;
    }
    function f() public {
        x = 1;
        uint y = g();
        assert(x == 2 || x == 1);
    }
    function h() public {
        x = 3;
    }
}
// ----
// Warning 2072: (282-288): Unused local variable.
// Warning 6328: (304-328): CHC: Assertion violation happens here.\nCounterexample:\na = false, x = 3, d = 0\n = 0\n\nTransaction trace:\nC.constructor()\nState: a = false, x = 0, d = 0\nC.g()\n    d.d() -- untrusted external call, synthesized as:\n        C.f() -- reentrant call\n            C.g() -- internal call\n                d.d() -- untrusted external call, synthesized as:\n                    C.h() -- reentrant call
