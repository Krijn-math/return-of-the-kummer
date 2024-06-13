//this file shows how to compute the point differences P+Q and P-Q given P and Q
//on the general and squared Kummer surface, using the biquadratics
//this is inspired by qDSA by Renes and Smith, Proposition 3 and 4 (2017/518)


if assigned is_main_script then
    filename := "file_loader.m";
    Write(filename, "\n" : Overwrite := true);
else
    is_main_script := true;
    print "point_diff.m is being executed directly.";
    filename := "file_loader.m";

    files := [
        "../costello-code/Params.m",
        "../costello-code/Kummer.m",
        "../costello-code/Maps.m",
        "../section2/invariants.m",
        "../section2/more_maps.m",
        "../section2/general.m",
        "../section4/biquadratic_general_kummer.m",
        "../section4/biquadratic_intermediate_kummer.m"
        ];
    Write(filename, "\n" : Overwrite := true);
    for file in files do
        tmp :=  "load '" cat file cat "'; \n"; 
        Write(filename, tmp);
    end for;
end if;
load "file_loader.m";

// load "../section2/general.m";
// load "../section4/biquadratic_general_kummer.m";

//lets start with known values, P and Q on the jacobian where we can comute S and D
P := Random(J_ros1);
Q := Random(J_ros1);
S := P + Q;
D := P - Q;

//we map all to the general kummer surface
P := K_ros1!P;
Q := K_ros1!Q;
S := K_ros1!S;
D := K_ros1!D;

//compute the biquadratics forms applied on P and Q
//and also compute the corresponding equations for S and D
//these should be equal up to a scalar
A := BiiMatrix(P, Q);
B := CheckMatrix(S, D);

lambda := A[1,1]/B[1,1];
CC := B;

//checks that they are equal up to a scalar
for i,j in [1..4] do CC[i,j] := lambda*B[i,j]; end for;
if A ne CC then
    "biquadratics failed on general kummer :(";
end if;

// now we want to actually compute either S or D on K_ros1
// without having done this on the Jacobian
// see Prop. 4 of qDSA

bipoly<Z1, Z2, Z3, Z4> := PolynomialRing(Fp, 4);
Z := [Z1, Z2, Z3, Z4];

function BiiEquations(P, Q)
    //first, derive the equations with unknowns Z_i that should hold for D and S
    A := BiiMatrix(P, Q);

    f := ZeroMatrix(bipoly, 4, 4);
    for i,j in [1..4] do
        f[i,j] := A[j,j]*Z[i]^2 - 2*A[i,j]*Z[i]*Z[j] + A[i,i]*Z[j]^2;
    end for;

    return f;
end function;

function PointDifferenceGeneric(P, Q)
    //now given the set of equations f, the points S and D should be solutions
    //so we can get their coordinates by one-by-one finding the right roots of f_ij
    //and find S or D (we dont know which is which)
    assert Parent(P) eq Parent(Q);

    f := BiiEquations(P, Q);
    // when setting Z1 = 1, the first row gives us all biquadratics in one of the vars
    X := [];
    X[1] := 1;
    f12 := UnivariatePolynomial(Evaluate(f[1,2], <X[1], Z[2], Z[3], Z[4]>));
    //choose one of the two roots, eval others with respect to this
    //this essentially means we will find one of the two, S or D, the other corresponds to the other choice of root
    X[2] := Roots(f12)[1][1];
    f13 := UnivariatePolynomial(Evaluate(f[1,3], <X[1], X[2], Z[3], Z[4]>));
    f23 := UnivariatePolynomial(Evaluate(f[2,3], <X[1], X[2], Z[3], Z[4]>));
    f14 := UnivariatePolynomial(Evaluate(f[1,4], <X[1], X[2], Z[3], Z[4]>));
    f24 := UnivariatePolynomial(Evaluate(f[2,4], <X[1], X[2], Z[3], Z[4]>));

    // now we need the common root for both
    X[3] := Roots(GCD(f13, f23))[1][1];
    X[4] := Roots(GCD(f14, f24))[1][1];

    res := Parent(P)!X;
    return res;
end function;

SorD := PointDifferenceGeneric(P, Q);

assert SorD in {S, D};
"point difference on general kummer works\n";

//now we want to do this for K^sqr, but note that the biquadratics
//are not elegant! W go K^sqr -> K^Int by H
//then we recover S or D on K^int, and map it back to K^sqr by H

// // For testing use the below:
P := Random(J_alpha);
Q := Random(J_alpha);
S := P + Q;
D := P - Q;

P_rosenhain := J_rosenhain!JKappa(P, kappa);      //mapped to the Rosenhain
P := RosenhainToKummer(P_rosenhain, ros, K);         //mapped down to the Kummer
assert OnKummer(P, K);

Q_rosenhain := J_rosenhain!JKappa(Q, kappa);      //mapped to the Rosenhain
Q := RosenhainToKummer(Q_rosenhain, ros, K);         //mapped down to the Kummer
assert OnKummer(Q, K);

S_rosenhain := J_rosenhain!JKappa(S, kappa);      //mapped to the Rosenhain
S := RosenhainToKummer(S_rosenhain, ros, K);         //mapped down to the Kummer
assert OnKummer(S, K);

D_rosenhain := J_rosenhain!JKappa(D, kappa);      //mapped to the Rosenhain
D := RosenhainToKummer(D_rosenhain, ros, K);         //mapped down to the Kummer
assert OnKummer(D, K);

Kint := IntermediateKummer(K);

Pint := H(P);
Qint := H(Q);
Sint := H(S);
Dint := H(D);

//first lets check again that our biquadratics were actually correct
A := BiiMatrix_int(Kint, Pint, Qint);
B := CheckMatrix(Sint, Dint);

lambda := A[1,1]/B[1,1];

for i,j in [1..4] do CC[i,j] := lambda*B[i,j]; end for;
if A ne CC then
    "biquadratics failed on intermediate kummer :(";
end if;


/// Now we want to do Proposition 4 in qDSA to get either Sint or Dint on Kint
// all of this is essentially the same as for the general kummer surface

bipoly<Z1, Z2, Z3, Z4> := PolynomialRing(Fp, 4);
Z := [Z1, Z2, Z3, Z4];

function BiiEquations_int(P, Q, Kint)
    A := BiiMatrix_int(Kint,P, Q);

    f := ZeroMatrix(bipoly, 4, 4);
    for i,j in [1..4] do
        f[i,j] := A[j,j]*Z[i]^2 - 2*A[i,j]*Z[i]*Z[j] + A[i,i]*Z[j]^2;
    end for;

    return f;
end function;

function PointDifferenceSquared(P, Q, K)
    assert OnKummer(P, K);
    assert OnKummer(Q, K);

    Kint := IntermediateKummer(K);

    Pint := H(P);
    Qint := H(Q);

    f := BiiEquations_int(Pint, Qint, Kint);
    // when setting Z1 = 1, the first row gives us all biquadratics in one of the vars
    X := [];
    X[1] := 1;
    f12 := UnivariatePolynomial(Evaluate(f[1,2], <X[1], Z[2], Z[3], Z[4]>));
    //choose one of the two roots, eval others with respect to this
    X[2] := Roots(f12)[1][1];
    f13 := UnivariatePolynomial(Evaluate(f[1,3], <X[1], X[2], Z[3], Z[4]>));
    f23 := UnivariatePolynomial(Evaluate(f[2,3], <X[1], X[2], Z[3], Z[4]>));
    f14 := UnivariatePolynomial(Evaluate(f[1,4], <X[1], X[2], Z[3], Z[4]>));
    f24 := UnivariatePolynomial(Evaluate(f[2,4], <X[1], X[2], Z[3], Z[4]>));

    // now we need the common root for both
    X[3] := Roots(GCD(f13, f23))[1][1];
    X[4] := Roots(GCD(f14, f24))[1][1];

    X := H([Fp!x : x in X]);
    assert OnKummer(X,K);
    return X;
end function;

function PointDifferenceSquaredBoth(P, Q, K)
    //here we simply return both S and D, by going through both roots
    //in the python code, this is optimized much further
    assert OnKummer(P, K);
    assert OnKummer(Q, K);

    Kint := IntermediateKummer(K);

    Pint := H(P);
    Qint := H(Q);

    /////////////////////////////
    //////    FIRST ROOT    /////
    /////////////////////////////

    f := BiiEquations_int(Pint, Qint, Kint);
    // when setting Z1 = 1, the first row gives us all biquadratics in one of the vars
    X := [];
    X[1] := 1;
    f12 := UnivariatePolynomial(Evaluate(f[1,2], <X[1], Z[2], Z[3], Z[4]>));
    //choose one of the two roots, eval others with respect to this
    X[2] := Roots(f12)[1][1]; saving := X[2];
    f13 := UnivariatePolynomial(Evaluate(f[1,3], <X[1], X[2], Z[3], Z[4]>));
    f23 := UnivariatePolynomial(Evaluate(f[2,3], <X[1], X[2], Z[3], Z[4]>));
    f14 := UnivariatePolynomial(Evaluate(f[1,4], <X[1], X[2], Z[3], Z[4]>));
    f24 := UnivariatePolynomial(Evaluate(f[2,4], <X[1], X[2], Z[3], Z[4]>));

    // now we need the common root for both
    X[3] := Roots(GCD(f13, f23))[1][1];
    X[4] := Roots(GCD(f14, f24))[1][1];

    X := H([Fp!x : x in X]);
    assert OnKummer(X,K);
    D := X;

    /////////////////////////////
    //////    SECOND ROOT    ////
    /////////////////////////////

    X := [];
    X[1] := 1;
    f12 := UnivariatePolynomial(Evaluate(f[1,2], <X[1], Z[2], Z[3], Z[4]>));
    f12 := f12 div (Parent(f12).1 - saving);
    //choose the other root
    X[2] := Roots(f12)[1][1];
    f13 := UnivariatePolynomial(Evaluate(f[1,3], <X[1], X[2], Z[3], Z[4]>));
    f23 := UnivariatePolynomial(Evaluate(f[2,3], <X[1], X[2], Z[3], Z[4]>));
    f14 := UnivariatePolynomial(Evaluate(f[1,4], <X[1], X[2], Z[3], Z[4]>));
    f24 := UnivariatePolynomial(Evaluate(f[2,4], <X[1], X[2], Z[3], Z[4]>));

    // now we need the common root for both
    X[3] := Roots(GCD(f13, f23))[1][1];
    X[4] := Roots(GCD(f14, f24))[1][1];

    X := H([Fp!x : x in X]);
    assert OnKummer(X,K);
    S := X;

    return D,S;
end function;


// // For testing
X,Y := PointDifferenceSquaredBoth(P, Q, K);
assert {normalise(X), normalise(Y)} eq {normalise(S), normalise(D)};

X := PointDifferenceSquared(P,Q,K);
assert normalise(X) in {normalise(S), normalise(D)};


"point difference on squared kummer works\n";
"point_diff.m done\n\n";

