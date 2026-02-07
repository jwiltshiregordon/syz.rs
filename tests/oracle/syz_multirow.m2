-- Oracle script: syz of multi-row matrices over ZZ[x,y]
-- Run: echo 'load "tests/oracle/syz_multirow.m2"' | M2 --silent --no-readline

-- Helper: print syzygy matrix columns in tuple format
-- M is the input matrix, S = syz M
doSyzMatrix = (R, M, label) -> (
    print("=== " | label | " ===");
    ngens := numColumns M;
    S := syz M;
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

----------------------------------------------------------------------
-- 2x3 matrices over ZZ[x,y]
----------------------------------------------------------------------
R = ZZ[x, y, MonomialOrder => GRevLex]
use R

-- 1. IDENTITY_LIKE: columns close to e_0, e_1
doSyzMatrix(R, matrix {{1, 0, x}, {0, 1, y}}, "IDENTITY_LIKE")

-- 2. LINEAR_2x3: all entries linear
doSyzMatrix(R, matrix {{x, y, x+y}, {y, x, x-y}}, "LINEAR_2x3")

-- 3. MIXED_DEGREE_2x3: mix of constants, linears, quadratics
doSyzMatrix(R, matrix {{x^2, y, 1}, {x, x*y, y^2}}, "MIXED_DEGREE_2x3")

-- 4. ZERO_COLUMN: one column is zero
doSyzMatrix(R, matrix {{x, 0, y}, {y, 0, x}}, "ZERO_COLUMN")

-- 5. RANK_1: all columns are scalar multiples of one vector
doSyzMatrix(R, matrix {{x, 2*x, 3*x}, {y, 2*y, 3*y}}, "RANK_1")

-- 6. COEFFICIENTS_2x3: entries with nontrivial ZZ coefficients
doSyzMatrix(R, matrix {{2*x, 3*y, 5}, {3, 2*x, 7*y}}, "COEFFICIENTS_2x3")

exit 0
