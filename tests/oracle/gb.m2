-- Oracle script: GB computation over ZZ with syzygies
-- Run: echo 'load "tests/oracle/gb.m2"' | M2 --silent --no-readline

-- Helper: print a polynomial (ring element) as sorted tuple list
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

-- Helper: print a vector (module element) as tuple list
printVecEntry = (v, n) -> (
    if v == 0 then (
        print "  []";
        return;
    );
    allTerms := {};
    for comp from 0 to n - 1 do (
        entry := v_comp;
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
)

-- Compute GB for an ideal (ring elements, component 0)
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

    -- Syzygies of the generators
    M := matrix {genList};
    S := syz M;
    ngens := #genList;
    print("syz (" | toString(numColumns S) | " elements):");
    for j from 0 to numColumns S - 1 do (
        print("  syz " | toString j | ":");
        v := S_{j};
        -- v is a column vector; extract as list
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

----------------------------------------------------------------------
-- 1-variable tests
----------------------------------------------------------------------
R1 = ZZ[x, MonomialOrder => GRevLex]
use R1

print "--- 1 variable ---"
doGBIdeal(R1, {x^2 + 1}, "SINGLE_GEN_1VAR")
doGBIdeal(R1, {2*x + 1, 4*x + 1}, "TWO_GEN_1VAR_A")
doGBIdeal(R1, {6*x + 1, 4*x + 1}, "TWO_GEN_1VAR_B")
doGBIdeal(R1, {6*x^2, 10*x^2, 15*x^2}, "THREE_GEN_1VAR")

----------------------------------------------------------------------
-- 2-variable tests
----------------------------------------------------------------------
R2 = ZZ[x, y, MonomialOrder => GRevLex]
use R2

doGBIdeal(R2, {x^2 + 1, y^2 + 1}, "COPRIME_LEADS_2VAR")
doGBIdeal(R2, {x^2 - y, x*y - x}, "CLASSIC_2VAR")
doGBIdeal(R2, {3*x + y, 2*x - y}, "COEFF_2VAR")
doGBIdeal(R2, {x + y, x + y}, "IDENTICAL_2VAR")
doGBIdeal(R2, {2*x, 3*x}, "SCALAR_MULT_2VAR")
doGBIdeal(R2, {x^2 + x*y, x*y + y^2}, "SIMILAR_2VAR")

----------------------------------------------------------------------
-- 3-variable tests
----------------------------------------------------------------------
R3 = ZZ[x, y, z, MonomialOrder => GRevLex]
use R3

doGBIdeal(R3, {x^2 + y + z, x*y + z, y^2 + x}, "CLASSIC_3VAR")
doGBIdeal(R3, {x + y + z - 1, x^2 + y^2 + z^2 - 1}, "KATSURA_LIKE_3VAR")
doGBIdeal(R3, {6*x + 4*y + 2*z, 3*x + 9*y + 6*z}, "LARGE_COEFF_3VAR")

-- Slightly bigger example
doGBIdeal(R3, {x^2 - y*z, x*y - z^2, y^2 - x*z}, "TWISTED_CUBIC_3VAR")

exit 0
