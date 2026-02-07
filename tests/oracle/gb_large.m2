-- Oracle script: larger GB examples over ZZ with more syzygies
-- Looking for 2-variable examples with 3+ syzygies
-- Run: echo 'load "tests/oracle/gb_large.m2"' | M2 --silent --no-readline

printPolyR = (f) -> (
    if f == 0 then (
        print "  []";
        return;
    );
    ts := terms f;
    result := "  [";
    for i from 0 to #ts - 1 do (
        t := ts#i;
        c := leadCoefficient t;
        e := flatten exponents leadMonomial t;
        comma := if i < #ts - 1 then ", " else "";
        result = result | "(" | toString c | ", " | toString e | ", 0)" | comma;
    );
    result = result | "]";
    print result;
)

doGBIdeal = (R, genList, label) -> (
    print("=== " | label | " ===");
    I := ideal genList;
    G := gb I;
    gbMat := gens G;
    gbList := flatten entries gbMat;
    print("gb (" | toString(#gbList) | " elements):");
    for i from 0 to #gbList - 1 do (
        print("  gb " | toString i | ":");
        printPolyR(gbList#i);
    );

    M := matrix {genList};
    S := syz M;
    ngens := #genList;
    print("syz (" | toString(numColumns S) | " elements):");
    for j from 0 to numColumns S - 1 do (
        print("  syz " | toString j | ":");
        v := S_{j};
        allTerms := {};
        for comp from 0 to ngens - 1 do (
            entry := v_(comp, 0);
            if entry != 0 then (
                ts := terms entry;
                for t in ts do (
                    c := leadCoefficient t;
                    e := flatten exponents leadMonomial t;
                    allTerms = append(allTerms, (c, e, comp));
                );
            );
        );
        result := "  [";
        for i from 0 to #allTerms - 1 do (
            triple := allTerms#i;
            comma := if i < #allTerms - 1 then ", " else "";
            result = result | "(" | toString triple#0 | ", " | toString triple#1 | ", " | toString triple#2 | ")" | comma;
        );
        result = result | "]";
        print result;
    );
    print "";
)

R = ZZ[x, y, MonomialOrder => GRevLex]
use R

-- Try various 2-var examples to find ones with 3+ syzygies

-- Three generators sharing lead monomial with different coefficients
doGBIdeal(R, {6*x^2 + x, 10*x^2 + y, 15*x^2 + 1}, "THREE_SAME_LEAD_2VAR")

-- Three generators, mixed
doGBIdeal(R, {x^2, x*y, y^2}, "MONOMIAL_IDEAL_2VAR")

-- Larger coefficients, three generators
doGBIdeal(R, {6*x + 4*y, 10*x + 9*y, 15*x + 2*y}, "THREE_LINEAR_2VAR")

-- Quadratics with three generators
doGBIdeal(R, {x^2 + 2*x*y + y^2, x^2 - y^2, 2*x*y}, "THREE_QUADRATIC_2VAR")

-- Four generators
doGBIdeal(R, {2*x^2 + 3*y, 3*x*y + 1, 5*y^2 + x, 7*x + 2*y}, "FOUR_GEN_2VAR")

-- ZZ-heavy: three generators with large coefficients
doGBIdeal(R, {6*x^2 + 4*x*y + 2, 10*x^2 + 5*y + 3, 15*x^2 + 7*x + 1}, "LARGE_THREE_GEN_2VAR")

-- Simple three generators producing interesting GB
doGBIdeal(R, {x^3, x^2*y, x*y^2 + y^3}, "CUBIC_2VAR")

exit 0
