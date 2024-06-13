if assigned is_main_script then
    filename := "file_loader.m";
    Write(filename, "\n" : Overwrite := true);
else
    is_main_script := true;
    print "compression.m is being executed directly.";
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
        "../section3/v2_and_new_pairings.m"
        ];
    Write(filename, "\n" : Overwrite := true);
    for file in files do
        tmp :=  "load '" cat file cat "'; \n"; 
        Write(filename, tmp);
    end for;
end if;
load "file_loader.m";

//load "../section3/v2_and_new_pairings.m";


//try to compress and decompress a random point on E_alpha
//first, we map it to the Kummer and lets call it R
//then we find a deterministic basis with good profiles P and Q
//and we run point_diff to get D
//we express R in terms of P and Q, e.g. P + [s_i]Q
//the compression is to return s_i

//for decompression, we simply rerun deterministic basis sampling
//to get P and Q, and point_diff for D
//then we use R' <-- xBIDIM(P, Q, D, s_i)  and check R = R'

///////////////////////////////////////////////////////////////
////////                                             //////////
////////              HELPER FUNCTION                //////////
////////                                             //////////
///////////////////////////////////////////////////////////////

//we will need the map up from v2.m
function JacPointAbove(P)
    //a rough way to find elements of the jacobian D_P that will map down to P
    //we first use the maps to find u0, u1, and v02
    //then find possible points on J that have the same mumford polynomial a(x)
    //then match up these points to have the right value v0^2 and return one
    u0, u1, v02 := Getvo2(P, K);

    poly<x> := PolynomialRing(Fp);
    ax := x^2 + u1*x + u0;
    possible := SetToSequence(Points(J_rosenhain, ax, 2));
    filter_possible := [ D : D in possible | Coefficients(D[2])[1]^2 eq v02 ];
    assert {P} eq {normalise(RosenhainToKummer(D, ros, K)) : D in filter_possible};

    return filter_possible[1];
end function;

///////////////////////////////////////////////////////////////
////////                                             //////////
////////              FROM SQISIGN CODE              //////////
////////                                             //////////
///////////////////////////////////////////////////////////////

// HyperEll curve function
function WorkDiscLog(R, P, Q, ell, ord)
    //this is the inner part of the discrete log function
    //as described by the SQIsign spec
    //this simply works on both Jacobians of genus 1 and genus 2 curves in Magma

    if ord eq 1 then
        for a,b in [0..ell] do
            Rp := a*P + b*Q;
            if R eq Rp then return a,b; end if;
        end for;
        print "error";
        assert 3 eq 5;
    end if;

    e := ord div 2;
    fac1 := ell^(ord - e);
    P1 := fac1*P; Q1 := fac1*Q; R1 := fac1*R;
    a1, b1 := WorkDiscLog(R1, P1, Q1, ell, e);

    fac2 := ell^(e);
    P2 := fac2*P; Q2 := fac2*Q; R2 := R - a1*P - b1*Q;
    a2, b2 := WorkDiscLog(R2, P2, Q2, ell, ord - e);

    // a1; a2;
    return a1 + a2*ell^e, b1 + b2*ell^e;
end function;

//Ell curve function
function DiscLog(R, P, Q, ell, ord)
    //the initial step required to compute the discrete log of R in terms of P and Q
    //that is, given R computes a and b such that R = aP + bQ
    //if you want to have a == 1, simply sample R and P of same profile, and return a^-1 b
    //then R and P + a^-1 b Q generate the same kernel

    //this is superseded by python code

    a, b := WorkDiscLog(R, P, Q, ell, ord);
    a := a mod ell^ord;
    b := b mod ell^ord;
    assert R eq a*P + b*Q;
    return a, b;
end function;


///////////////////////////////////////////////////////////////
////////                                             //////////
////////              THREE POINT LADDER             //////////
////////                                             //////////
///////////////////////////////////////////////////////////////


//on elliptic curves
//p + 1 is divisible by 2^f
f := Valuation(p+1, 2);

//here we do some testing. We take P and Q in a somewhat rough way
// then create a random R = P+ sQ. We then recompute a and b using our function defined above
repeat P := Random(E_alpha); P := ((p+1) div 2^f)*P; until Order(P) eq 2^f;
Q := P;
repeat P := Random(E_alpha); P := ((p+1) div 2^f)*P; 
until Order(P) eq 2^f and (2^(f-1)) * P ne (2^(f-1)) * Q;

R := P + Random([1..p])*Q;

a, b := DiscLog(R, P, Q, 2, f);
assert a eq 1;
assert R eq P + b*Q;

//so we have verified that it works on elliptic curves!

//we now try a similar approach on Kummers
f := Valuation(p+1, 2) - 1;
cofac := (p+1) div 2^(f+1);

//we wont know which of these two it will be because we dont know PpQ or PmQ
//so we simply try both (as we do when computing the PointDifference)
JR := FullToJac(P+b*Q);
JR2 := FullToJac(P - b*Q);
KR := normalise(FullToKummer(P + b*Q));
KR2 := normalise(FullToKummer(P - b*Q));

KP := FullToKummer(P);
KQ := FullToKummer(Q);

//we compute both differences
//superseded in python by a function that simply returns both of them
KD := PointDifferenceSquared(KP, KQ, K);       
_, KS := DBLADD(KP, KQ, Invert4Constants(KD), K);

//one of these three point ladders is then equal to R = P + bQ
//we indicate the right choice with a single bit in the signature
KRp := ThreePointLadder(KP, KQ, KD, b, K);
KRp2 := ThreePointLadder(KP, KQ, KS, b, K);
if {KRp, KRp2} eq {KR, KR2} then
    "three point ladder on Kummer WORKS";
else
    "three point ladder on Kummer FAILED";
end if;


///////////////////////////////////////////////////////////////
////////                                             //////////
////////              BASIS SAMPLING                 //////////
////////                                             //////////
///////////////////////////////////////////////////////////////

function RandomPointFromJac(K)
    //sample a random point on K that originates from J(Fp) and not its twist J^T(Fp)
    //see PointOrigin in the paper for more details.
    repeat
        Pp := RandomKummerPoint(K); 
        u0, u1, v02 := Getvo2(Pp, K);
    until IsSquare(v02);

    return Pp, u0, u1, v02;
end function;

function SpecificPointFromJac(K, i)
    //these functions allow to generate points on Jac with a specific short description
    repeat
        repeat
            i +:= 1;
            t, Pp := SpecificKummerPoint(K, [1,2,i,0]); 
        until t eq true;
        u0, u1, v02 := Getvo2(Pp, K);
    until IsSquare(v02);

    return Pp, u0, u1, v02;
end function;

function PointWithProfile(prof, K)
    //these functions allow to generate points on Jac with a specific short description and with a profile matching the provided profile
    i := 1;
    repeat 
        i +:= 1;
        Pp, u0, u1, v02 := SpecificPointFromJac(K, i);
    until SmallProfile(Pp, K) eq prof;
    return Pp;
end function;

function FirstBasisPoint(K)
    //this cheats a little bit, by looking for a point with a profile that is similar to KP
    //in python is done properly using the precomputed right profiles
    return PointWithProfile(SmallProfile(KP,K), K);
end function;

function SecondBasisPoint(K)
    //this cheats a little bit, by looking for a point with a profile that is similar to KP
    //in python is done properly using the precomputed right profiles
    return PointWithProfile(SmallProfile(KQ,K), K);
end function;


///////////////////////////////////////////////////////////////
////////                                             //////////
////////              POINT COMPRESSION              //////////
////////                                             //////////
///////////////////////////////////////////////////////////////


//we now try to express R in terms of basis points on K

function SampleDeterministicBasis(K)
    //first sample a deterministic basis for Im(E_alpha) on K
    //e.g. the image of the Z/(p+1/2)^2 subgroup of J
    Pp := FirstBasisPoint(K);
    Pp := KummerScalar(Pp, K, cofac);


    Qp := SecondBasisPoint(K);
    Qp := KummerScalar(Qp, K, cofac);

    assert KummerScalar(Pp, K, 2^f) eq K[2];
    assert KummerScalar(Qp, K, 2^f) eq K[2];
    return Pp, Qp;
end function;

function KummerDiscLog(R, P, Q)
    //raise the points P, Q, R to the Jacobian as JP, JQ, JR,
    //then compute the discrete log on the jacobian and return a and b
    // where JR = aJP + bJQ on the jacobin
    assert KummerScalar(R, K, 2^f) eq K[2];

    JP := JacPointAbove(P);
    JQ := JacPointAbove(Q);
    JKR := JacPointAbove(R);

    disc_log_worked := false;
    try
        a, b := DiscLog(JKR, JP, JQ, 2, f);
        disc_log_worked := true;
        print "DiscreteLog on kummer WORKED";
    catch e
        print "DiscreteLog on kummer FAILED";
    end try;

    return a, b;
end function;

//lets see if it works!
Pp, Qp := SampleDeterministicBasis(K);

a, b := KummerDiscLog(KR, Pp, Qp);

//bit of an akwward way to compute R = aP + bQ
//fixed in the python by ensuring a = 1
aPp := KummerScalar(Pp, K, a);
aDp, aSp := PointDifferenceSquaredBoth(aPp, Qp, K);

//we dont know beforehand if we get aP + bQ or aP - bQ
//depends on having chosen D or S
//thus needs 1 bit to communicate this
resD := normalise(ThreePointLadder(aPp, Qp, aDp, b, K));
resS := normalise(ThreePointLadder(aPp, Qp, aSp, b, K));
if KR in {resD, resS} then
    print "point compression on kummer (via Jac) WORKS";
else
    print "point compression on kummer FAILED";
end if;

"compression.m done";

