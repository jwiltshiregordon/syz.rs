-- Oracle script: ZZ coefficient operations
-- Run: echo 'load "tests/oracle/zz.m2"' | M2 --silent --no-readline

-- syzygy(a,b) returns (x,y) with ax + by = 0
-- In M2, this is an internal ring operation. Over ZZ:
-- g = gcd(a,b), x = -b/g, y = a/g

-- We can test via the syz command on 1x2 matrices over ZZ
R = ZZ

printSyz = (a, b) -> (
    M := matrix {{a, b}};
    S := syz M;
    -- S is a 2x? matrix; take first column
    x := S_(0,0);
    y := S_(1,0);
    print("syzygy(" | toString a | ", " | toString b | ") = (" | toString x | ", " | toString y | ")");
    print("  check: " | toString(a*x + b*y));
)

print "=== SYZYGY ==="
printSyz(6, 4)
printSyz(12, 8)
printSyz(7, 3)
printSyz(1, 1)
printSyz(0, 5)
printSyz(5, 0)
printSyz(-6, 4)
printSyz(6, -4)
printSyz(-6, -4)
printSyz(15, 10)
printSyz(100, 35)

print "=== GCD ==="
gcdPairs = {{6,4}, {12,8}, {7,3}, {0,5}, {5,0}, {1,1}, {-6,4}, {15,10}, {100,35}, {0,0}}
for p in gcdPairs do (
    a := p#0;
    b := p#1;
    print("gcd(" | toString a | ", " | toString b | ") = " | toString(gcd(a,b)));
)

-- For balanced remainder, M2 uses the convention:
-- balrem(a, b) is in (-|b|/2, |b|/2]
-- We test via manual computation since M2 doesn't directly expose this.
-- Actually M2's % operator gives non-negative remainder. Let's just verify our
-- understanding with regular quotient/remainder.

print "=== DIVREM ==="
divRemPairs = {{17,5}, {-17,5}, {17,-5}, {-17,-5}, {10,3}, {-10,3}, {0,7}, {7,1}, {15,5}}
for p in divRemPairs do (
    a := p#0;
    b := p#1;
    q := a // b;
    r := a % b;
    print("divrem(" | toString a | ", " | toString b | ") = (" | toString q | ", " | toString r | ")");
    print("  check: " | toString(q*b + r) | " == " | toString a);
)

-- Content removal: gcd of all coefficients, made positive
print "=== CONTENT ==="
S = ZZ[x,y,z, MonomialOrder => GRevLex]
polys = {6*x^2 + 4*x*y + 2, -15*x^2*y + 10*x - 5, 7*x + 3*y, x + y + z}
for f in polys do (
    c := content f;  -- M2's content function (from Macaulay2Doc)
    -- Actually, in M2, `content` returns an ideal. Let's use a different approach.
    -- Let's just compute gcd of coefficients manually.
    coeffList := flatten entries (coefficients f)_1;
    coeffInts := apply(coeffList, c -> lift(c, ZZ));
    g := fold(gcd, coeffInts);
    print("poly: " | toString f);
    print("  content: " | toString g);
    print("  primitive: " | toString(f // g));
)

exit 0
