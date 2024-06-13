//this file combines two thing in the paper, namely the result in section 2
//on an efficient map K --> J to recover u0, u1 and v02
//which is used in two subsequent applications
// 1. first, v02 can be used to check if a point arises from J(Fp) or J^T(Fp)
// 2. second, u0 and u1 can be used to compute 2-pairings on J instead of K

if assigned is_main_script then
    filename := "file_loader.m";
    Write(filename, "\n" : Overwrite := true);
else
    is_main_script := true;
    print "v2_and_new_pairings.m is being executed directly.";
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
        "../section2/add_matrices_squared.m"
        ];
    Write(filename, "\n" : Overwrite := true);
    for file in files do
        tmp :=  "load '" cat file cat "'; \n"; 
        Write(filename, tmp);
    end for;
end if;
load "file_loader.m";

// load "../section4/point_diff.m";
// load "../section3/fastkummerpairings.m";
// load "../section2/add_matrices_squared.m";


w3, w4, w5, w6 := Explode([1] cat ros);
poly<u0,u1,lambda> := PolynomialRing(Fp, 3);
f1 := u0*(w3*w5 - u0)*(w4 + w6 + u1);
f2 := u0*(w4*w6 - u0)*(w3 + w5 + u1);
f3 := u0*(w3*w6 - u0)*(w4 + w5 + u1);
f4 := u0*(w4*w5 - u0)*(w3 + w6 + u1);
fi := [f1, f2, f3, f4];

///////////////////////////////////////////////////////////////
////////                                             //////////
////////           New approach K --> J              //////////
////////                                             //////////
///////////////////////////////////////////////////////////////

function CorrectPoint(P, K)
    return [P[i]/K[2][i] : i in [1..4]];
end function;

function GetU_helper(P, K)
    //a helper function to evaluate the formulas from the paper
    X := CorrectPoint(P, K);

    //all the ff should be equal to v0^2
    //ff := [ fi[i] - lambda*X[i] : i in [1..4]];

    //these formulas are derived in proofs/v2_derive.m
    u0_top := ((w3 - w5)*w4*w6*X[1] + (w4 - w6)*w3*w5*X[2] - (w3 - w6)*w4*w5*X[3] - (w4 - w5)*w3*w6*X[4]);
    u0_bot := (w4 - w6)*X[1] + (w3 - w5)*X[2] - (w4 - w5)*X[3] - (w3 - w6)*X[4];
    u1_top := -(X[1] + X[2] - X[3] - X[4])*(w3*w4 - w5*w6);
    u1_bot := u0_bot;

    return u0_top, u0_bot, u1_top, u1_bot, X[1];
end function;

function GetU(P, K)
    //turns the projective results into affine
    u0_top, u0_bot, u1_top, u1_bot := GetU_helper(P, K);

    u0 := u0_top/u0_bot;
    u1 := u1_top/u1_bot;

    return u0, u1;
end function;

function Getvo2(P, K)
    //first computes the u0 and u1 values, and uses those to find v02
    //uses the results from section 2 and 4 of the paper
    u0_top, u0_bot, u1_top, u1_bot, X1 := GetU_helper(P, K);

    u0 := u0_top/u0_bot;
    u1 := u1_top/u1_bot;

    lambda_top := -(w3 - w4)*(w5 - w6)*(w3*w4 - w5*w6)*u0_top;
    lambda_bot := u0_bot^2;
    lambda := lambda_top/lambda_bot;

    //manual evaluation in fi[1] - lambda*X[1]
    //could be any of the fi, we just picked one
    if DBL(P, K) ne K[2] then
        v02 := u0*(w3*w5 - u0)*(w4 + w6 + u1) - lambda*X1;
        return u0, u1, v02;
    end if;

    return u0, u1, 0;
end function;

//lets test that the map Kummer --> Jac works
for i in [1..100] do
    D := Random(J_rosenhain);
    P := RosenhainToKummer(D, ros, K);
    lambda := Random(Fp);
    P := [lambda*p : p in P];
    u0, u1, v02 := Getvo2(P, K);
    assert u0 eq Coefficients(D[1])[1];
    assert u1 eq Coefficients(D[1])[2];

    original_v0 := (Coefficients(D[2])[1]);
    assert v02 eq original_v0^2;
end for;
"New map Kummer --> Jac WORKS";

///////////////////////////////////////////////////////////////
////////                                             //////////
////////           NEW PAIRINGS WITH v02             //////////
////////                                             //////////
///////////////////////////////////////////////////////////////


//if IsSquare(v02) over Fp, then P comes from Jac,
//otherwise, its precisely nonsquare and comes from Jac^T

//furthermore, finding these u0 and u1 so easily
//allows for very easy pairings :-)

//two helper functions needed later, but a bit ugly
//both of these are not needed when sampling the points in a smarter way
//only needed when the point P is not coprime on the kummer
function Identify(P, K)
    //identifies for a 2-torsion point P which indices ij are such that P = L_ij
    //can be much improved given the formulas for the 2-torsion points in section 2

    P := normalise(P);
    assert DBL(P, K) eq K[2];

    //very ugly, sorry, can be done much better
    for i,j in [2..6] do if i lt j then
        Dtmp := J_rosenhain![(x - wp[i])*(x - wp[j]), 0];
        Ptmp := RosenhainToKummer(Dtmp, ros, K);
        if P eq normalise(Ptmp) then return i,j; end if;
    end if; end for;

    for j in [2..6] do if i lt j then
        Dtmp := J_rosenhain![(x - wp[j]), 0];
        Ptmp := RosenhainToKummer(Dtmp, ros, K);
        if P eq normalise(Ptmp) then return 1,j; end if;
    end if; end for;

    "error";
    return [0,0,0,0];
end function;

function ReIdentify(indices, K)
    //returns L_ij given ij
    //can be much improved given the formulas for the 2-torsion points in section 2

    i := indices[1];
    j := indices[2];
    D := J_rosenhain![(x - wp[i])*(x - wp[j]), 0];
    return RosenhainToKummer(D, ros, K);
end function;

//now the pairing, simply a la Jac actually

function NewPairing(index, P, K)
    //assumes coprimality, e.g. P is not of order 2 and shares no weierstrass point on the curve
    i := index[1];
    j := index[2];

    assert i lt j;

    u0, u1, T := Getvo2(P, K);

    wi := wp[i];
    wj:= wp[j];

    if i eq 1 then
        //the case where inf is in L_ij, which we can ignore
        return wj^2 + wj*u1 + u0;
    end if;

    res :=  wi^2*wj^2 + wi^2*wj*u1 + wi^2*u0 + wi*wj^2*u1 + wi*wj*u1^2 + wi*u0*u1 + wj^2*u0 
    + wj*u0*u1 + u0^2;

    if res ne 0 then
        //the nice case, coprimality between L_ij and P
        return res;
    end if;

    //this means we reach non-coprimality between L_ij and P. There are two cases
    //1) P is of order 2, just add a random point on the Kummer and use W_P
    // this makes eval easy
    if DBL(P, K) eq K[2] then
        T := RandomKummerPoint(K);

        //get the index for the point P of order 2
        i2, j2 := Identify(P, K);

        res1 := NewPairing(index, WW[i2,j2](T), K);
        res2 := NewPairing(index, T, K);
        return res1/res2;
    else
    //2) P is not of order 2, just add a correct order two point S and use W_S
        i2 := Random([1..6]); j2 := Random([i2..6]);
        res1 := NewPairing(index, ApplyWW(i2,j2,P), K);
        
        //get the point Li2j2 for the index i2, j2
        Li2j2 := ReIdentify(i2, j2);

        res2 := NewPairing(index, Li2j2, K);
        return res1/res2;
    end if;

end function;

function NewProfile(P, K)
    //returns the profile of a point P using the new pairing defined above
    return [IsSquare(NewPairing(<i,j>, P, K)) : i,j in [1..6] | i lt j];
end function;

triv_prof := [ true, true, true, true, true, true, true, true, true, true, true, true, true, 
true, true ];

//some trivial tests regarding the pairing
for i in [1..10] do
    P := RandomKummerPoint(K);
    T := KummerScalar(P, K, (p+1) div 4);
    if T ne K[2] then
        assert NewProfile(P, K) ne triv_prof;
        assert NewProfile(DBL(P,K), K) eq triv_prof;
    end if;
end for;
"New Pairing using v02 WORKS";
"v2.m done\n";
