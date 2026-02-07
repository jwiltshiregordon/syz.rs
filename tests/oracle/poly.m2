-- Oracle script: generate polynomial test fixtures for Rust tests.
-- Output format: simple text, one test case per block.
-- Run: echo 'load "tests/oracle/poly.m2"' | M2 --silent --no-readline

R = ZZ[x,y,z, MonomialOrder => GRevLex]

-- Helper: print a polynomial as a list of (coeff, [exp vector], component) terms
-- For ring elements (not module elements), component is always 0.
printPoly = (f) -> (
    if f == 0 then (
        print "[]";
        return;
    );
    ts := terms f;
    print "[";
    for i from 0 to #ts - 1 do (
        t := ts#i;
        c := leadCoefficient t;
        e := flatten exponents leadMonomial t;
        comma := if i < #ts - 1 then "," else "";
        print("  (" | toString c | ", [" | demark(",", apply(e, toString)) | "], 0)" | comma);
    );
    print "]";
)

print "=== ADD ==="
-- Test: f + g
f = 3*x^2*y - 2*x*z + 5
g = -x^2*y + 4*x*z + y^2 - 3
print "f:"
printPoly f
print "g:"
printPoly g
print "f+g:"
printPoly(f + g)

print "=== ADD_CANCEL ==="
-- Test: addition with cancellation
f = 2*x^2 + 3*x*y + z
g = -2*x^2 - 3*x*y + 2*z
print "f:"
printPoly f
print "g:"
printPoly g
print "f+g:"
printPoly(f + g)

print "=== NEGATE ==="
f = 3*x^2*y - 2*x*z + 5
print "f:"
printPoly f
print "-f:"
printPoly(-f)

print "=== SCALAR_MUL ==="
f = 3*x^2*y - 2*x*z + 5
print "f:"
printPoly f
print "3*f:"
printPoly(3*f)
print "-2*f:"
printPoly(-2*f)

print "=== TERM_MUL ==="
-- multiply by 2*x*y
f = 3*x^2*y - 2*x*z + 5
print "f:"
printPoly f
print "2*x*y * f:"
printPoly(2*x*y * f)

print "=== ZERO ==="
f = 3*x - 3*x
print "f:"
printPoly f

print "=== LEAD_TERM ==="
f = 3*x^2*y - 2*x*z + 5
print "f:"
printPoly f
print "leadTerm:"
printPoly(leadTerm f)
print "leadCoefficient:"
print(leadCoefficient f)
print "leadMonomial exponents:"
print(flatten exponents leadMonomial f)

print "=== SORTING ==="
-- Verify grevlex sorting: terms should come out in descending grevlex order
f = z^2 + x^2 + y^2 + x*y + x*z + y*z
print "f:"
printPoly f

print "=== SUB ==="
f = 3*x^2*y - 2*x*z + 5
g = x^2*y + 4*x*z - 1
print "f:"
printPoly f
print "g:"
printPoly g
print "f-g:"
printPoly(f - g)

exit 0
