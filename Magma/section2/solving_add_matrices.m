// this file finds the W_ij matrices that represent addition by a two torsion point L_ij, specifically for the elliptic Kummer
// it does so using the approach sketched in Section 2 of the paper.
// it then matches the values in W_ij to known values, and includes a script to verify the correctness
// it also includes a script to generate LaTeX code for these matrices

// NOTE: the more general W_ij for the squared Kummer are found using wij_squared_kummer.m

if assigned is_main_script then
    filename := "file_loader.m";
    Write(filename, "\n" : Overwrite := true);
else
    is_main_script := true;
    print "solving_add_matrices.m is being executed directly.";
    filename := "file_loader.m";

    files := [
        "../costello-code/Params.m",
        "../costello-code/Kummer.m",
        "../costello-code/Maps.m",
        "../section2/invariants.m",
        "../section2/more_maps.m",
        "../section2/general.m",
        "../section4/biquadratic_general_kummer.m",
        "../section4/biquadratic_intermediate_kummer.m",
        "../section4/point_diff.m",
        "../section3/gaudry_code.m",
        "../section3/fastkummerpairings.m",
        "../section2/add_matrices_squared.m",
        "../section3/v2_and_new_pairings.m",
        "../section3/robert_pairings.m"
        ];
    Write(filename, "\n" : Overwrite := true);
    for file in files do
        tmp :=  "load '" cat file cat "'; \n"; 
        Write(filename, tmp);
    end for;
end if;
load "file_loader.m";

//load "../section3/robert_pairings.m";

////////////////////////////////////////////////////////

function SolveMatrix(i,j)
    //just the setup
    n := 4;     //dimension of our kummer
    m := 20;    //number of points we will interpolate
    R<[X]> := PolynomialRing(Fp, n^2 + m, "grevlex");
    
    //unknowns for our matrix we try to find
    Ax := Matrix(R, n, n, X[1..n^2]);
    
    //to correct for the projective factor in our solutions
    D := DiagonalMatrix(R, m, X[n^2 + 1..n^2 + m]);

    //the 2-torsion point that we will add by (naming irrelevant)
    if i ne 1 then
        J35 := J_rosenhain![(x - wp[i])*(x - wp[j]) ,0]; 
    else //we include infinity by ignoring it
        J35 := J_rosenhain![(x - wp[j]) ,0]; 
    end if;    
    K35 := RosenhainToKummer(J35, ros, K); 

    JP := [ Random(J_rosenhain) : i in [1..m]];
    JP35 := [ P + J35 : P in JP ];

    // our input points, e.g. random Kummer points
    KP := [ RosenhainToKummer(P, ros, K) : P in JP];
    KP := [ [R!p : p in P] : P in KP];

    // our output points, e.g. random kummer points + a specific 2-torsion point
    KP35 := [ RosenhainToKummer(P, ros, K) : P in JP35];
    KP35 := [ [R!p : p in P] : P in KP35];

    preprocessKP := [ Transpose(Matrix(Vector(p))) : p in KP];
    V := HorizontalJoin(preprocessKP);

    preprocessKP35 := [ Transpose(Matrix(Vector(p))) : p in KP35];
    W := HorizontalJoin(preprocessKP35);
    
    //interpolating
    S := Ax*V - W*D;

    //this just finds the solutions for A
    GB := GroebnerBasis(Eltseq(S)); 
    GG := GB[1..16];
    Xtmp := X;
    Xtmp[36] := 1;
    GGeval := [ Evaluate(g, Xtmp) : g in GG];
    RR := [ Roots(UnivariatePolynomial(g))[1][1] : g in GGeval ];

    Sol := X; 
    for i in [1..n^2] do Sol[i] := RR[i]; end for; 
    for i in [n^2 + 1..n^2 + m] do Sol[i] := 0; end for; 
    A := Evaluate(Ax, Sol);

    //A is correct, but scaled by random factors...
    //putting the first nonzero to 1 usually helps
    for i,j in [1..4] do
        if A[i,j] ne 0 then return 1/A[i,j]*A; end if;
    end for;
end function;

function Cleaner(A)
    //helper function that was needed for Magma reasons.
    // just maps A / Fp2 to B / Fp whenever A has only Fp values.

    B := ZeroMatrix(Fp, 4, 4);
    for i,j in [1..4] do B[i,j] := Fp!A[i,j]; end for;
    return B;
end function;

SolMatrices := [ Cleaner(SolveMatrix(i,j)) : i,j in [1..6] | i lt j ];

values := {}; 

//essentially what we need to explain
for A in SolMatrices do values := values join Set(Eltseq(A)); end for;
know := [0, 1, -1,
          tau,  1/tau, 
         -tau, -1/tau,
          tau^2,  1/tau^2, 
          -tau^2,  -1/tau^2, 
         (mu1 - tau)/(mu2 - tau),
        -(mu1 - tau)/(mu2 - tau),
         (mu1 - 1/tau)/(mu2 - 1/tau),
        -(mu1 - 1/tau)/(mu2 - 1/tau),
         tau*(mu1 - tau)/(mu2 - tau),
        -tau*(mu1 - tau)/(mu2 - tau),
         1/tau*(mu1 - tau)/(mu2 - tau),
        -1/tau*(mu1 - tau)/(mu2 - tau),
        tau*(mu1 - 1/tau)/(mu2 - 1/tau),
        -tau*(mu1 - 1/tau)/(mu2 - 1/tau),
         1/tau*(mu1 - 1/tau)/(mu2 - 1/tau),
        -1/tau*(mu1 - 1/tau)/(mu2 - 1/tau)
         ];

text := [ "0", "1", "-1",
          "tau",  "1/tau", 
         "-tau", "-1/tau",
          "tau^2", " 1/tau^2", 
          "-tau^2", " -1/tau^2",
         "(mu1 - tau)/(mu2 - tau)",
        "-(mu1 - tau)/(mu2 - tau)",
        "(mu1 - 1/tau)/(mu2 - 1/tau)",
        "-(mu1 - 1/tau)/(mu2 - 1/tau)",
        "tau*(mu1 - tau)/(mu2 - tau)",
        "-tau*(mu1 - tau)/(mu2 - tau)",
        " 1/tau*(mu1 - tau)/(mu2 - tau)",
        "-1/tau*(mu1 - tau)/(mu2 - tau)",
        "tau*(mu1 - 1/tau)/(mu2 - 1/tau)",
        "-tau*(mu1 - 1/tau)/(mu2 - 1/tau)",
        "1/tau*(mu1 - 1/tau)/(mu2 - 1/tau)",
        "-1/tau*(mu1 - 1/tau)/(mu2 - 1/tau)"
         ];

latex := [ "0", "1", "-1",
          " \\tau",  "\\tilde{\\tau}", 
         "- \\tau", "- \\tilde{\\tau}",
          " \\tau^2", "\\tilde{\\tau}^2", 
          "- \\tau^2", "-\\tilde{\\tau}^2",
         "\\gamma",
        "-\\gamma",
        "\\tilde{\\gamma}",
        "-\\tilde{\\gamma}",
        " \\tau \\cdot \\gamma",
        "- \\tau \\cdot \\gamma",
        " \\tilde{\\tau} \\cdot \\gamma",
        "-\\tilde{\\tau} \\cdot \\gamma",
        " \\tau \\cdot \\tilde{\\gamma}",
        "- \\tau \\cdot \\tilde{\\gamma}",
        "\\tilde{\\tau} \\cdot \\tilde{\\gamma}",
        "-\\tilde{\\tau} \\cdot \\tilde{\\gamma}"
         ];

assert Set(know) eq values;

function ValuesToText(A)
    MatchA := ZeroMatrix(Integers(), 4, 4);
    for i,j in [1..4] do
        MatchA[i,j] := Index(know, A[i,j]); 
    end for;

    TextA := [ [ text[a] : a in Eltseq(MatchA[i])]  : i in [1..4] ];
    return TextA;
end function;

function ValuesToLaTeX(A)
    MatchA := ZeroMatrix(Integers(), 4, 4);
    for i,j in [1..4] do
        MatchA[i,j] := Index(know, A[i,j]); 
    end for;

    for i in [1..4] do
        latex[MatchA[i][1]] cat " & " cat latex[MatchA[i][2]] cat " & " cat latex[MatchA[i][3]] cat " & " cat latex[MatchA[i][4]] cat " \\\\ ";
    end for;
    return 0;
end function;

//quick script that gives the output below
// for i in [1..5] do for j in [i+1..6] do
//     printf "\nM%o%o := Matrix(", i,j;
//     printf "%o);\n", ValuesToText(SolveMatrix(i,j));
//     printf "assert SolveMatrix(%o, %o) eq M%o%o;\n", i,j,i,j;
// end for; end for;


//due to tau --> 1/tau symmetry we get 
//symmetry between (3,6) and (4,5)
//sometimes we need to resolve this
//by picking the right tau --> 1/tau
//we decide this based on a 2-torsion point that has tau
J35 := J_rosenhain![(x - wp[3])*(x - wp[5]), 0];
P35 := RosenhainToKummer(J35, ros, K);
P35 := [P35[i]/P35[4] : i in [1..4]];
P := P35;

if P[3] ne (mu1 - 1/tau)/(mu2 - 1/tau) then
    tau := 1/tau;
end if;

M12 := Matrix([
    [ 0, 1, 0, 0 ],
    [ 1, 0, 0, 0 ],
    [ 0, 0, 0, 1 ],
    [ 0, 0, 1, 0 ]
]);
assert SolveMatrix(1, 2) eq M12;

M13 := Matrix([
    [ 1, -(mu1 - tau)/(mu2 - tau), tau*(mu1 - tau)/(mu2 - tau), -tau ],
    [ (mu1 - tau)/(mu2 - tau), -1, tau, -tau*(mu1 - tau)/(mu2 - tau) ],
    [ tau*(mu1 - tau)/(mu2 - tau), -tau, 1, -(mu1 - tau)/(mu2 - tau) ],
    [ tau, -tau*(mu1 - tau)/(mu2 - tau), (mu1 - tau)/(mu2 - tau), -1 ]
]);
assert SolveMatrix(1, 3) eq M13;

M14 := Matrix([
    [ 1, -(mu1 - tau)/(mu2 - tau),  1/tau*(mu1 - tau)/(mu2 - tau), -1/tau ],
    [ (mu1 - tau)/(mu2 - tau), -1, 1/tau, -1/tau*(mu1 - tau)/(mu2 - tau) ],
    [  1/tau*(mu1 - tau)/(mu2 - tau), -1/tau, 1, -(mu1 - tau)/(mu2 - tau) ],
    [ 1/tau, -1/tau*(mu1 - tau)/(mu2 - tau), (mu1 - tau)/(mu2 - tau), -1 ]
]);
assert SolveMatrix(1, 4) eq M14;

M15 := Matrix([
    [ 1, -(mu1 - 1/tau)/(mu2 - 1/tau), -1/tau, 1/tau*(mu1 - 1/tau)/(mu2 - 1/tau) ],
    [ (mu1 - 1/tau)/(mu2 - 1/tau), -1, -1/tau*(mu1 - 1/tau)/(mu2 - 1/tau), 1/tau ],
    [ 1/tau, -1/tau*(mu1 - 1/tau)/(mu2 - 1/tau), -1, (mu1 - 1/tau)/(mu2 - 1/tau) ],
    [ 1/tau*(mu1 - 1/tau)/(mu2 - 1/tau), -1/tau, -(mu1 - 1/tau)/(mu2 - 1/tau), 1 ]
]);
assert SolveMatrix(1, 5) eq M15;

M16 := Matrix([
    [ 1, -(mu1 - 1/tau)/(mu2 - 1/tau), -tau, tau*(mu1 - 1/tau)/(mu2 - 1/tau) ],
    [ (mu1 - 1/tau)/(mu2 - 1/tau), -1, -tau*(mu1 - 1/tau)/(mu2 - 1/tau), tau ],
    [ tau, -tau*(mu1 - 1/tau)/(mu2 - 1/tau), -1, (mu1 - 1/tau)/(mu2 - 1/tau) ],
    [ tau*(mu1 - 1/tau)/(mu2 - 1/tau), -tau, -(mu1 - 1/tau)/(mu2 - 1/tau), 1 ]
]);
assert SolveMatrix(1, 6) eq M16;

M23 := Matrix([
    [ 1, -(mu1 - 1/tau)/(mu2 - 1/tau), tau*(mu1 - 1/tau)/(mu2 - 1/tau), -tau ],
    [ (mu1 - 1/tau)/(mu2 - 1/tau), -1, tau, -tau*(mu1 - 1/tau)/(mu2 - 1/tau) ],
    [ tau*(mu1 - 1/tau)/(mu2 - 1/tau), -tau, 1, -(mu1 - 1/tau)/(mu2 - 1/tau) ],
    [ tau, -tau*(mu1 - 1/tau)/(mu2 - 1/tau), (mu1 - 1/tau)/(mu2 - 1/tau), -1 ]
]);
assert SolveMatrix(2, 3) eq M23;

M24 := Matrix([
    [ 1, -(mu1 - 1/tau)/(mu2 - 1/tau), 1/tau*(mu1 - 1/tau)/(mu2 - 1/tau), -1/tau ],
    [ (mu1 - 1/tau)/(mu2 - 1/tau), -1, 1/tau, -1/tau*(mu1 - 1/tau)/(mu2 - 1/tau) ],
    [ 1/tau*(mu1 - 1/tau)/(mu2 - 1/tau), -1/tau, 1, -(mu1 - 1/tau)/(mu2 - 1/tau) ],
    [ 1/tau, -1/tau*(mu1 - 1/tau)/(mu2 - 1/tau), (mu1 - 1/tau)/(mu2 - 1/tau), -1 ]
]);
assert SolveMatrix(2, 4) eq M24;

M25 := Matrix([
    [ 1, -(mu1 - tau)/(mu2 - tau), -1/tau,  1/tau*(mu1 - tau)/(mu2 - tau) ],
    [ (mu1 - tau)/(mu2 - tau), -1, -1/tau*(mu1 - tau)/(mu2 - tau), 1/tau ],
    [ 1/tau, -1/tau*(mu1 - tau)/(mu2 - tau), -1, (mu1 - tau)/(mu2 - tau) ],
    [  1/tau*(mu1 - tau)/(mu2 - tau), -1/tau, -(mu1 - tau)/(mu2 - tau), 1 ]
]);
assert SolveMatrix(2, 5) eq M25;

M26 := Matrix([
    [ 1, -(mu1 - tau)/(mu2 - tau), -tau, tau*(mu1 - tau)/(mu2 - tau) ],
    [ (mu1 - tau)/(mu2 - tau), -1, -tau*(mu1 - tau)/(mu2 - tau), tau ],
    [ tau, -tau*(mu1 - tau)/(mu2 - tau), -1, (mu1 - tau)/(mu2 - tau) ],
    [ tau*(mu1 - tau)/(mu2 - tau), -tau, -(mu1 - tau)/(mu2 - tau), 1 ]
]);
assert SolveMatrix(2, 6) eq M26;

M34 := Matrix([
    [ 0, 0, 0, 1 ],
    [ 0, 0, 1, 0 ],
    [ 0, 1, 0, 0 ],
    [ 1, 0, 0, 0 ]
]);
assert SolveMatrix(3, 4) eq M34;

M35 := Matrix([
    [ 1, 1, -tau, -1/tau ],
    [ 1, 1, -1/tau, -tau ],
    [ tau, 1/tau, -1, -1 ],
    [ 1/tau, tau, -1, -1 ]
]);
assert SolveMatrix(3, 5) eq M35;

M36 := Matrix([
    [ 1,  1/tau^2, -1/tau, -1/tau ],
    [  1/tau^2, 1, -1/tau, -1/tau ],
    [ 1/tau, 1/tau, -1,  -1/tau^2 ],
    [ 1/tau, 1/tau,  -1/tau^2, -1 ]
]);
assert SolveMatrix(3, 6) eq M36;

M45 := Matrix([
    [ 1, tau^2, -tau, -tau ],
    [ tau^2, 1, -tau, -tau ],
    [ tau, tau, -1, -tau^2 ],
    [ tau, tau, -tau^2, -1 ]
]);
assert SolveMatrix(4, 5) eq M45;

M46 := Matrix([
    [ 1, 1, -1/tau, -tau ],
    [ 1, 1, -tau, -1/tau ],
    [ 1/tau, tau, -1, -1 ],
    [ tau, 1/tau, -1, -1 ]
]);
assert SolveMatrix(4, 6) eq M46;

M56 := Matrix([
    [ 0, 0, 1, 0 ],
    [ 0, 0, 0, 1 ],
    [ 1, 0, 0, 0 ],
    [ 0, 1, 0, 0 ]
]);
assert SolveMatrix(5, 6) eq M56;

"All addition by two matrices verified";



//quick script for printing the right TeX
// for i in [1..5] do for j in [i+1..6] do
//     printf "\n\\[\nW_{%o,%o} := \\begin{pmatrix}\n", i,j;
//     a := ValuesToLaTeX(SolveMatrix(i,j));
//     printf "\\end{pmatrix}\n\\]\n";
// end for; end for;
