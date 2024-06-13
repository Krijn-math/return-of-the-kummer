// this file finds the W_ij matrices that represent addition by a two torsion point L_ij 
// it does so using the approach sketched in Section 2 of the paper.
// it then matches the values in W_ij to known values, and includes a script to verify the correctness
// it also includes a script to generate LaTeX code for these matrices

// NOTE: these matrices are not elegant for squared Kummer surfaces, and only somewhat elegent for elliptic Kummer surfaces.

"trying to find correct matrices";

p := 2^128 - 34827;


Fp := FiniteField(p);
Fp2<i> := FiniteField(p^2);
poly<x> := PolynomialRing(Fp);
poly2<X> := PolynomialRing(Fp2);

load "tmp_load.m";

lam := Fp!4577873896448729347807790734465324421;
mu := Fp!234789861994364729479821884660190521407;
nu := Fp!174333573523192164016359058694895260480;

ros := [lam, mu, nu];
wp := [0, 0, 1] cat ros;
CC := HyperellipticCurve(&*[x - wi : wi in wp[2..6]]);
JJ := Jacobian(CC);

function RosenhainToMu(ros)
    lam, mu, nu := Explode(ros);
    mu2 := Sqrt( (mu*(mu - 1)*(lam-nu)) / (nu*(nu-1)*(lam-mu)) );
    mu3 := Sqrt(lam*mu/nu);
    mu4 := 1;
    mu1 := mu2*mu3*nu/mu;
    return [mu1, mu2, mu3, mu4];
end function;

mus := RosenhainToMu(ros);
a, b, c, d := Explode(mus);
A, B, C, D := Explode(H(mus));

K := SquaredKummerFromSquaredThetas(mus);

f := Valuation(p+1, 2);


////////////////////////////////////////////////////////
/// trying to solve

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
        J35 := JJ![(x - wp[i])*(x - wp[j]) ,0]; 
    else //we include infinity by ignoring it
        J35 := JJ![(x - wp[j]) ,0]; 
    end if;    
    K35 := RosenhainToKummer(J35, ros, K); 

    JP := [ Random(JJ) : i in [1..m]];
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
    B := ZeroMatrix(Fp, 4, 4);
    for i,j in [1..4] do B[i,j] := Fp!A[i,j]; end for;
    return B;
end function;

SolMatrices := [ Cleaner(SolveMatrix(i,j)) : i,j in [1..6] | i lt j ];

values := {}; 

//essentially what we need to explain
for A in SolMatrices do values := values join Set(Eltseq(A)); end for;

rough_init := [1, -1] cat [wp[i] - wp[j] : i,j in [2..6] | i ne j];
rough_div := [1, -1] cat [rough_init[i]/rough_init[j] : i,j in [1..#rough_init] | i ne j];
mus_div := [1, -1] cat [mus[i]/mus[j] : i,j in [1..4] | i ne j];

rough := {};

for first in rough_div do
    for second in mus_div do
        if first*second in values then
            rough := rough join {first*second};
        end if;
    end for;
end for;

rough := SetToSequence(rough);

assert #rough eq 22;

roughdiv := [rough[i]/rough[j] : i,j in [1..#rough] | i ne j];
for i in roughdiv do 
    if i notin rough and i in values then 
        Append(~rough, i); 
    end if; 
end for;

rough := Set([0] cat rough);

assert rough eq values;

"we know all values!";

know := [Fp!0, Fp!1, Fp!-1
         ];


text := [ "0", "1", "-1"
//        "-1/tau*(mu1 - 1/tau)/(mu2 - 1/tau)"
         ];

latex := [ "0", "1", "-1"
//        "-\\tilde{\\tau} \\cdot \\tilde{\\gamma}"
         ];

for i1, i2, i3, i4 in [2..6] do
    if i3 ne i4 then
        for i5, i6 in [1..4] do
            tmp := (wp[i1] - wp[i2])/(wp[i3] - wp[i4])*mus[i5]/mus[i6];
            if tmp in values and tmp notin know then
                Append(~know, tmp);
                Append(~text, Sprintf("(wp[%o] - wp[%o])/(wp[%o] - wp[%o])*mus[%o]/mus[%o]", i1, i2, i3, i4, i5, i6));
                Append(~latex, Sprintf("\\frac{w_%o - w_%o}{w_%o - w_%o} \\cdot \\frac{\\mu_%o}{\\mu_%o}", i1, i2, i3, i4, i5, i6));
            end if;
        end for;
    end if;
end for;

assert #know gt 22;

for i,j in [1..#know] do
    if know[i] ne know[j] and know[j] ne 0 then
        tmp := know[i]/know[j];
        if tmp in values and tmp notin know then
            //"THIS HAPPENS";
            Append(~know, tmp);
            Append(~text, text[i] cat "/(" cat text[j] cat ")");
            Append(~latex, latex[i] cat "\\left(" cat latex[j] cat "\\right)^{-1}");
        end if;
    end if;
end for;

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


M12 := Matrix([
[ 0, 1, 0, 0 ],
[ 1, 0, 0, 0 ],
[ 0, 0, 0, 1 ],
[ 0, 0, 1, 0 ]
]);
assert SolveMatrix(1, 2) eq M12;

M13 := Matrix([
[ 1, (wp[2] - wp[5])/(wp[3] - wp[2])*mus[4]/mus[3], (wp[2] - wp[5])/(wp[2] - 
wp[3])*mus[4]/mus[3]/((wp[3] - wp[5])/(wp[4] - wp[5])*mus[3]/mus[2]), (wp[4] - 
wp[5])/(wp[5] - wp[3])*mus[2]/mus[3] ],
[ (wp[2] - wp[5])/(wp[2] - wp[3])*mus[4]/mus[3], -1, (wp[4] - wp[5])/(wp[3] - 
wp[5])*mus[2]/mus[3], (wp[2] - wp[5])/(wp[2] - wp[3])*mus[4]/mus[3]/((wp[3] - 
wp[5])/(wp[5] - wp[4])*mus[3]/mus[2]) ],
[ (wp[2] - wp[5])/(wp[2] - wp[3])*mus[4]/mus[3]/((wp[3] - wp[5])/(wp[4] - 
wp[5])*mus[3]/mus[2]), (wp[4] - wp[5])/(wp[5] - wp[3])*mus[2]/mus[3], 1, (wp[2] 
- wp[5])/(wp[3] - wp[2])*mus[4]/mus[3] ],
[ (wp[4] - wp[5])/(wp[3] - wp[5])*mus[2]/mus[3], (wp[2] - wp[5])/(wp[2] - 
wp[3])*mus[4]/mus[3]/((wp[3] - wp[5])/(wp[5] - wp[4])*mus[3]/mus[2]), (wp[2] - 
wp[5])/(wp[2] - wp[3])*mus[4]/mus[3], -1 ]
]);
assert SolveMatrix(1, 3) eq M13;

M14 := Matrix([
[ 1, (wp[2] - wp[5])/(wp[3] - wp[2])*mus[4]/mus[3], (wp[2] - wp[5])/(wp[2] - 
wp[3])*mus[4]/mus[3]/((wp[4] - wp[5])/(wp[3] - wp[5])*mus[2]/mus[3]), (wp[3] - 
wp[5])/(wp[5] - wp[4])*mus[3]/mus[2] ],
[ (wp[2] - wp[5])/(wp[2] - wp[3])*mus[4]/mus[3], -1, (wp[3] - wp[5])/(wp[4] - 
wp[5])*mus[3]/mus[2], (wp[2] - wp[5])/(wp[2] - wp[3])*mus[4]/mus[3]/((wp[4] - 
wp[5])/(wp[5] - wp[3])*mus[2]/mus[3]) ],
[ (wp[2] - wp[5])/(wp[2] - wp[3])*mus[4]/mus[3]/((wp[4] - wp[5])/(wp[3] - 
wp[5])*mus[2]/mus[3]), (wp[3] - wp[5])/(wp[5] - wp[4])*mus[3]/mus[2], 1, (wp[2] 
- wp[5])/(wp[3] - wp[2])*mus[4]/mus[3] ],
[ (wp[3] - wp[5])/(wp[4] - wp[5])*mus[3]/mus[2], (wp[2] - wp[5])/(wp[2] - 
wp[3])*mus[4]/mus[3]/((wp[4] - wp[5])/(wp[5] - wp[3])*mus[2]/mus[3]), (wp[2] - 
wp[5])/(wp[2] - wp[3])*mus[4]/mus[3], -1 ]
]);
assert SolveMatrix(1, 4) eq M14;

M15 := Matrix([
[ 1, (wp[2] - wp[3])/(wp[5] - wp[2])*mus[3]/mus[4], (wp[3] - wp[6])/(wp[5] - 
wp[3])*mus[2]/mus[4], (wp[2] - wp[3])/(wp[2] - wp[5])*mus[3]/mus[4]/((wp[3] - 
wp[5])/(wp[3] - wp[6])*mus[4]/mus[2]) ],
[ (wp[2] - wp[3])/(wp[2] - wp[5])*mus[3]/mus[4], -1, (wp[2] - wp[3])/(wp[2] - 
wp[5])*mus[3]/mus[4]/((wp[3] - wp[5])/(wp[6] - wp[3])*mus[4]/mus[2]), (wp[3] - 
wp[6])/(wp[3] - wp[5])*mus[2]/mus[4] ],
[ (wp[3] - wp[6])/(wp[3] - wp[5])*mus[2]/mus[4], (wp[2] - wp[3])/(wp[2] - 
wp[5])*mus[3]/mus[4]/((wp[3] - wp[5])/(wp[6] - wp[3])*mus[4]/mus[2]), -1, (wp[2]
- wp[3])/(wp[2] - wp[5])*mus[3]/mus[4] ],
[ (wp[2] - wp[3])/(wp[2] - wp[5])*mus[3]/mus[4]/((wp[3] - wp[5])/(wp[3] - 
wp[6])*mus[4]/mus[2]), (wp[3] - wp[6])/(wp[5] - wp[3])*mus[2]/mus[4], (wp[2] - 
wp[3])/(wp[5] - wp[2])*mus[3]/mus[4], 1 ]
]);
assert SolveMatrix(1, 5) eq M15;

M16 := Matrix([
[ 1, (wp[2] - wp[3])/(wp[5] - wp[2])*mus[3]/mus[4], (wp[3] - wp[5])/(wp[6] - 
wp[3])*mus[4]/mus[2], (wp[2] - wp[3])/(wp[2] - wp[5])*mus[3]/mus[4]/((wp[3] - 
wp[6])/(wp[3] - wp[5])*mus[2]/mus[4]) ],
[ (wp[2] - wp[3])/(wp[2] - wp[5])*mus[3]/mus[4], -1, (wp[2] - wp[3])/(wp[2] - 
wp[5])*mus[3]/mus[4]/((wp[3] - wp[6])/(wp[5] - wp[3])*mus[2]/mus[4]), (wp[3] - 
wp[5])/(wp[3] - wp[6])*mus[4]/mus[2] ],
[ (wp[3] - wp[5])/(wp[3] - wp[6])*mus[4]/mus[2], (wp[2] - wp[3])/(wp[2] - 
wp[5])*mus[3]/mus[4]/((wp[3] - wp[6])/(wp[5] - wp[3])*mus[2]/mus[4]), -1, (wp[2]
- wp[3])/(wp[2] - wp[5])*mus[3]/mus[4] ],
[ (wp[2] - wp[3])/(wp[2] - wp[5])*mus[3]/mus[4]/((wp[3] - wp[6])/(wp[3] - 
wp[5])*mus[2]/mus[4]), (wp[3] - wp[5])/(wp[6] - wp[3])*mus[4]/mus[2], (wp[2] - 
wp[3])/(wp[5] - wp[2])*mus[3]/mus[4], 1 ]
]);
assert SolveMatrix(1, 6) eq M16;

M23 := Matrix([
[ 1, (wp[2] - wp[3])/(wp[5] - wp[2])*mus[3]/mus[4], (wp[2] - wp[3])/(wp[2] - 
wp[5])*mus[3]/mus[4]/((wp[3] - wp[5])/(wp[4] - wp[5])*mus[3]/mus[2]), (wp[4] - 
wp[5])/(wp[5] - wp[3])*mus[2]/mus[3] ],
[ (wp[2] - wp[3])/(wp[2] - wp[5])*mus[3]/mus[4], -1, (wp[4] - wp[5])/(wp[3] - 
wp[5])*mus[2]/mus[3], (wp[2] - wp[3])/(wp[2] - wp[5])*mus[3]/mus[4]/((wp[3] - 
wp[5])/(wp[5] - wp[4])*mus[3]/mus[2]) ],
[ (wp[2] - wp[3])/(wp[2] - wp[5])*mus[3]/mus[4]/((wp[3] - wp[5])/(wp[4] - 
wp[5])*mus[3]/mus[2]), (wp[4] - wp[5])/(wp[5] - wp[3])*mus[2]/mus[3], 1, (wp[2] 
- wp[3])/(wp[5] - wp[2])*mus[3]/mus[4] ],
[ (wp[4] - wp[5])/(wp[3] - wp[5])*mus[2]/mus[3], (wp[2] - wp[3])/(wp[2] - 
wp[5])*mus[3]/mus[4]/((wp[3] - wp[5])/(wp[5] - wp[4])*mus[3]/mus[2]), (wp[2] - 
wp[3])/(wp[2] - wp[5])*mus[3]/mus[4], -1 ]
]);
assert SolveMatrix(2, 3) eq M23;

M24 := Matrix([
[ 1, (wp[2] - wp[3])/(wp[5] - wp[2])*mus[3]/mus[4], (wp[2] - wp[3])/(wp[2] - 
wp[5])*mus[3]/mus[4]/((wp[4] - wp[5])/(wp[3] - wp[5])*mus[2]/mus[3]), (wp[3] - 
wp[5])/(wp[5] - wp[4])*mus[3]/mus[2] ],
[ (wp[2] - wp[3])/(wp[2] - wp[5])*mus[3]/mus[4], -1, (wp[3] - wp[5])/(wp[4] - 
wp[5])*mus[3]/mus[2], (wp[2] - wp[3])/(wp[2] - wp[5])*mus[3]/mus[4]/((wp[4] - 
wp[5])/(wp[5] - wp[3])*mus[2]/mus[3]) ],
[ (wp[2] - wp[3])/(wp[2] - wp[5])*mus[3]/mus[4]/((wp[4] - wp[5])/(wp[3] - 
wp[5])*mus[2]/mus[3]), (wp[3] - wp[5])/(wp[5] - wp[4])*mus[3]/mus[2], 1, (wp[2] 
- wp[3])/(wp[5] - wp[2])*mus[3]/mus[4] ],
[ (wp[3] - wp[5])/(wp[4] - wp[5])*mus[3]/mus[2], (wp[2] - wp[3])/(wp[2] - 
wp[5])*mus[3]/mus[4]/((wp[4] - wp[5])/(wp[5] - wp[3])*mus[2]/mus[3]), (wp[2] - 
wp[3])/(wp[2] - wp[5])*mus[3]/mus[4], -1 ]
]);
assert SolveMatrix(2, 4) eq M24;

M25 := Matrix([
[ 1, (wp[2] - wp[5])/(wp[3] - wp[2])*mus[4]/mus[3], (wp[3] - wp[6])/(wp[5] - 
wp[3])*mus[2]/mus[4], (wp[2] - wp[5])/(wp[2] - wp[3])*mus[4]/mus[3]/((wp[3] - 
wp[5])/(wp[3] - wp[6])*mus[4]/mus[2]) ],
[ (wp[2] - wp[5])/(wp[2] - wp[3])*mus[4]/mus[3], -1, (wp[2] - wp[5])/(wp[2] - 
wp[3])*mus[4]/mus[3]/((wp[3] - wp[5])/(wp[6] - wp[3])*mus[4]/mus[2]), (wp[3] - 
wp[6])/(wp[3] - wp[5])*mus[2]/mus[4] ],
[ (wp[3] - wp[6])/(wp[3] - wp[5])*mus[2]/mus[4], (wp[2] - wp[5])/(wp[2] - 
wp[3])*mus[4]/mus[3]/((wp[3] - wp[5])/(wp[6] - wp[3])*mus[4]/mus[2]), -1, (wp[2]
- wp[5])/(wp[2] - wp[3])*mus[4]/mus[3] ],
[ (wp[2] - wp[5])/(wp[2] - wp[3])*mus[4]/mus[3]/((wp[3] - wp[5])/(wp[3] - 
wp[6])*mus[4]/mus[2]), (wp[3] - wp[6])/(wp[5] - wp[3])*mus[2]/mus[4], (wp[2] - 
wp[5])/(wp[3] - wp[2])*mus[4]/mus[3], 1 ]
]);
assert SolveMatrix(2, 5) eq M25;

M26 := Matrix([
[ 1, (wp[2] - wp[5])/(wp[3] - wp[2])*mus[4]/mus[3], (wp[3] - wp[5])/(wp[6] - 
wp[3])*mus[4]/mus[2], (wp[2] - wp[5])/(wp[2] - wp[3])*mus[4]/mus[3]/((wp[3] - 
wp[6])/(wp[3] - wp[5])*mus[2]/mus[4]) ],
[ (wp[2] - wp[5])/(wp[2] - wp[3])*mus[4]/mus[3], -1, (wp[2] - wp[5])/(wp[2] - 
wp[3])*mus[4]/mus[3]/((wp[3] - wp[6])/(wp[5] - wp[3])*mus[2]/mus[4]), (wp[3] - 
wp[5])/(wp[3] - wp[6])*mus[4]/mus[2] ],
[ (wp[3] - wp[5])/(wp[3] - wp[6])*mus[4]/mus[2], (wp[2] - wp[5])/(wp[2] - 
wp[3])*mus[4]/mus[3]/((wp[3] - wp[6])/(wp[5] - wp[3])*mus[2]/mus[4]), -1, (wp[2]
- wp[5])/(wp[2] - wp[3])*mus[4]/mus[3] ],
[ (wp[2] - wp[5])/(wp[2] - wp[3])*mus[4]/mus[3]/((wp[3] - wp[6])/(wp[3] - 
wp[5])*mus[2]/mus[4]), (wp[3] - wp[5])/(wp[6] - wp[3])*mus[4]/mus[2], (wp[2] - 
wp[5])/(wp[3] - wp[2])*mus[4]/mus[3], 1 ]
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
[ 1, (wp[3] - wp[5])/(wp[4] - wp[6])*mus[1]/mus[2], (wp[3] - wp[5])/(wp[6] - 
wp[3])*mus[4]/mus[2], (wp[3] - wp[5])/(wp[5] - wp[4])*mus[3]/mus[2] ],
[ (wp[3] - wp[5])/(wp[4] - wp[6])*mus[1]/mus[2], 1, (wp[3] - wp[5])/(wp[5] - 
wp[4])*mus[3]/mus[2], (wp[3] - wp[5])/(wp[6] - wp[3])*mus[4]/mus[2] ],
[ (wp[3] - wp[5])/(wp[3] - wp[6])*mus[4]/mus[2], (wp[3] - wp[5])/(wp[4] - 
wp[5])*mus[3]/mus[2], -1, (wp[3] - wp[5])/(wp[6] - wp[4])*mus[1]/mus[2] ],
[ (wp[3] - wp[5])/(wp[4] - wp[5])*mus[3]/mus[2], (wp[3] - wp[5])/(wp[3] - 
wp[6])*mus[4]/mus[2], (wp[3] - wp[5])/(wp[6] - wp[4])*mus[1]/mus[2], -1 ]
]);
assert SolveMatrix(3, 5) eq M35;

M36 := Matrix([
[ 1, (wp[3] - wp[6])/(wp[4] - wp[5])*mus[3]/mus[4], (wp[3] - wp[6])/(wp[5] - 
wp[3])*mus[2]/mus[4], (wp[3] - wp[5])/(wp[5] - wp[4])*mus[3]/mus[2] ],
[ (wp[3] - wp[6])/(wp[4] - wp[5])*mus[3]/mus[4], 1, (wp[3] - wp[5])/(wp[5] - 
wp[4])*mus[3]/mus[2], (wp[3] - wp[6])/(wp[5] - wp[3])*mus[2]/mus[4] ],
[ (wp[3] - wp[6])/(wp[3] - wp[5])*mus[2]/mus[4], (wp[3] - wp[5])/(wp[4] - 
wp[5])*mus[3]/mus[2], -1, (wp[3] - wp[6])/(wp[5] - wp[4])*mus[3]/mus[4] ],
[ (wp[3] - wp[5])/(wp[4] - wp[5])*mus[3]/mus[2], (wp[3] - wp[6])/(wp[3] - 
wp[5])*mus[2]/mus[4], (wp[3] - wp[6])/(wp[5] - wp[4])*mus[3]/mus[4], -1 ]
]);
assert SolveMatrix(3, 6) eq M36;

M45 := Matrix([
[ 1, (wp[4] - wp[5])/(wp[3] - wp[6])*mus[4]/mus[3], (wp[3] - wp[5])/(wp[6] - 
wp[3])*mus[4]/mus[2], (wp[4] - wp[5])/(wp[5] - wp[3])*mus[2]/mus[3] ],
[ (wp[4] - wp[5])/(wp[3] - wp[6])*mus[4]/mus[3], 1, (wp[4] - wp[5])/(wp[5] - 
wp[3])*mus[2]/mus[3], (wp[3] - wp[5])/(wp[6] - wp[3])*mus[4]/mus[2] ],
[ (wp[3] - wp[5])/(wp[3] - wp[6])*mus[4]/mus[2], (wp[4] - wp[5])/(wp[3] - 
wp[5])*mus[2]/mus[3], -1, (wp[4] - wp[5])/(wp[6] - wp[3])*mus[4]/mus[3] ],
[ (wp[4] - wp[5])/(wp[3] - wp[5])*mus[2]/mus[3], (wp[3] - wp[5])/(wp[3] - 
wp[6])*mus[4]/mus[2], (wp[4] - wp[5])/(wp[6] - wp[3])*mus[4]/mus[3], -1 ]
]);
assert SolveMatrix(4, 5) eq M45;

M46 := Matrix([
[ 1, (wp[4] - wp[6])/(wp[3] - wp[5])*mus[2]/mus[1], (wp[3] - wp[6])/(wp[5] - 
wp[3])*mus[2]/mus[4], (wp[4] - wp[5])/(wp[5] - wp[3])*mus[2]/mus[3] ],
[ (wp[4] - wp[6])/(wp[3] - wp[5])*mus[2]/mus[1], 1, (wp[4] - wp[5])/(wp[5] - 
wp[3])*mus[2]/mus[3], (wp[3] - wp[6])/(wp[5] - wp[3])*mus[2]/mus[4] ],
[ (wp[3] - wp[6])/(wp[3] - wp[5])*mus[2]/mus[4], (wp[4] - wp[5])/(wp[3] - 
wp[5])*mus[2]/mus[3], -1, (wp[4] - wp[6])/(wp[5] - wp[3])*mus[2]/mus[1] ],
[ (wp[4] - wp[5])/(wp[3] - wp[5])*mus[2]/mus[3], (wp[3] - wp[6])/(wp[3] - 
wp[5])*mus[2]/mus[4], (wp[4] - wp[6])/(wp[5] - wp[3])*mus[2]/mus[1], -1 ]
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
for i in [1..5] do for j in [i+1..6] do
    printf "\n\\[\nW_{%o,%o} := \\begin{pmatrix}\n", i,j;
    a := ValuesToLaTeX(SolveMatrix(i,j));
    printf "\\end{pmatrix}\n\\]\n";
end for; end for;
