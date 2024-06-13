/* 
    This file shows how elegant sampling, as described in section 4, works
    Note that the corresponding Python code is optimized further
*/

if assigned is_main_script then
    filename := "file_loader.m";
    Write(filename, "\n" : Overwrite := true);
else
    is_main_script := true;
    print "elegant_sampling.m is being executed directly.";
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

// load "../section2/general.m";
// load "../section3/v2_and_new_pairings.m";

lambda, mu, nu := Explode(ros);

second_order := [ 1 - lambda, 1 - mu, 1 - nu, lambda - mu, mu - nu, nu - lambda];

/////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////
/////////                SETUP                  /////////
/////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////


// From the Lemma in the paper, we get the following IsSquare values
// true         lambda
// false        mu
// false        nu
// false        1 - lambda
// true         1 - mu
// true         1 - nu
// true         lambda - mu
// true         mu - nu
// false        nu - lambda


// So, it means we can sample points from C with very precise profiles
// We determine the profile using (1,2), (1,3), (1,5) and (1,6)
// these are consistent on our Kummer surfaces

SamplingIndices := [ <1,2>, <1,3>, <1,5>, <1,6>];

function SamplingProfile(P, K)
    //computes a profile using the v2-pairing for the indices given by SamplingIndices
  assert OnKummer(P, K);

  return < IsSquare(NewPairing(indices, P, K)) select 1 else -1 : indices in SamplingIndices >;
end function;

function SamplingProfileNonVerbose(P, K)
    //computes a profile using the v2-pairing for the indices given by SamplingIndices
  assert OnKummer(P, K);

  return < IsSquare(NewPairing(indices, P, K)) : indices in SamplingIndices >;
end function;


//the points derived from E_alpha on K have specific 2-profiles!
//thats because they lie in a very specific subset of points with orders divisble by 2^f2
GoodProfiles := { SamplingProfile(FullToKummer(Random(E_alpha)),K) : i in [1..100]};
GoodProfiles := [ prof : prof in GoodProfiles | prof ne <1, 1, 1, 1>];

//we should get the following, excluding the trivial profile, which aligns to the random points sampled in [2]E
// [ <1, -1, -1, -1>, <1, 1, -1, 1>, <1, -1, 1, -1> ]

function RandomFromCurve()
    // we use the trick of sampling a point on K by sampling a random point P1 on C
    // and computing D_P = (P1) + (lambda, 0) on the Jacobian
    // we map this down
    // this will never give all points on K, but we only need pseudo-random points as we are trying
    // to deterministically sample a basis for the 2^f2 torsion

    //here, we try to sample such a point with a given profile and asserting that the two methods to compute these are equal
    P := Random(C_rosenhain); xp := P[1];
    W_fixed := C_rosenhain![ros[1], 0];
    D := J_rosenhain!(Divisor(P) + Divisor(W_fixed));
    P := RosenhainToKummer(D, ros, K);

    first_profile := SamplingProfileNonVerbose(P, K);
    second_profile := 
        < IsSquare(xp), IsSquare(xp-1), IsSquare(xp - mu), IsSquare(xp - nu) >;
    assert first_profile eq second_profile;
    return P, second_profile;
end function; 

// so now if we want to sample a point on K with lets say the first profile in
// GoodProfiles, we want xp to be square and xp -1 to be non-square

// first making them NonVerbose
GoodProfiles := { SamplingProfileNonVerbose(FullToKummer(Random(E_alpha)),K) : i in [1..100]};
GoodProfiles := [ prof : prof in GoodProfiles | prof ne <true, true, true, true>];


/////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////
/////////          ELEGANT SAMPLING             /////////
/////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////



//then the smart sampling for the profile <1, -1, ...>
FirstFp := [ Fp!x : x in [1..100]];

//precompute the right Fp values that have the requirements we need for the subprofile
//that is, x is a square but x-1 is not
Xs := [ x : x in FirstFp | IsSquare(x) and not IsSquare(x - 1)];
list_of_xs := [];
for xp in Xs do
    //then sample the point on C with that x-coordinate
    Ps := Points(C_rosenhain, Fp!xp);
    if #Ps gt 0 then
        P := Random(Ps);
        //we can check the profile just given this x-value
        profile := 
        < IsSquare(xp), IsSquare(xp-1), IsSquare(xp - mu), IsSquare(xp - nu) >;
        if profile in GoodProfiles then
            Append(~list_of_xs, xp);
        end if;
    end if;
end for;
//the good points can be mapped down to K
//because of laziness we do that manually here

xp := list_of_xs[1];
u0 := xp*w4;
u1 := -(xp+w4);
rhs := xp*(xp-1)*(xp-lambda)*(xp-mu)*(xp-nu);
v02 := (lambda/(xp-w4))^2*rhs;
assert IsSquare(v02);

//comparing to actual points
P := Random(Points(C_rosenhain, xp));
W := Random(Points(C_rosenhain, w4));
JP := J_rosenhain!(Divisor(P) + Divisor(W));

X1 := K[2][1]*(u0*(w3*w5-u0)*(w4+w6+u1)-v02);
X2 := K[2][2]*(u0*(w4*w6-u0)*(w3+w5+u1)-v02);
X3 := K[2][3]*(u0*(w3*w6-u0)*(w4+w5+u1)-v02);
X4 := K[2][4]*(u0*(w4*w5-u0)*(w3+w6+u1)-v02);

//hence Pp is a point as we are looking for
Pp := [X1,X2,X3,X4];


//we now do the same thing for an orthogonal profile
//then the smart sampling for the profile <1, 1, ...>
Xs := [ x : x in FirstFp | IsSquare(x) and IsSquare(x - 1)];
list_of_xs := [];
for xp in Xs do
    Ps := Points(C_rosenhain, Fp!xp);
    if #Ps gt 0 then
        P := Random(Ps);
        profile := 
        < IsSquare(xp), IsSquare(xp-1), IsSquare(xp - mu), IsSquare(xp - nu) >;
        if profile in GoodProfiles then
            Append(~list_of_xs, xp);
        end if;
    end if;

end for;

xp := list_of_xs[1];
u0 := xp*w4;
u1 := -(xp+w4);
rhs := xp*(xp-1)*(xp-lambda)*(xp-mu)*(xp-nu);
v02 := (lambda/(xp-w4))^2*rhs;
assert IsSquare(v02);

//comparing to actual points
Q := Random(Points(C_rosenhain, xp));
W := Random(Points(C_rosenhain, w4));
JQ := J_rosenhain!(Divisor(P) + Divisor(W));

X1 := K[2][1]*(u0*(w3*w5-u0)*(w4+w6+u1)-v02);
X2 := K[2][2]*(u0*(w4*w6-u0)*(w3+w5+u1)-v02);
X3 := K[2][3]*(u0*(w3*w6-u0)*(w4+w5+u1)-v02);
X4 := K[2][4]*(u0*(w4*w5-u0)*(w3+w6+u1)-v02);

//and we also have Qp on K, which should be orthogonal to Pp
//in other words, Pp and Qp are an implicit basis for Im(E_a[2^f2])
Qp := [X1,X2,X3,X4];


assert OnKummer(Pp, K);
assert OnKummer(Qp, K);

"elegant_sampling.m works";

//total cost given a random x in Xs is
// - 1 Sqrt to check if on C and get y, if yes then
//      - 1 Sqrt to check IsSquare(xp - mu) and
//      - 1 Sqrt to check IsSquare(xp - nu)
// if profile is OK then
// - 1M to get u0 and u1, 1I + 1M  + 1S to get v02 
//     per X_i
// - 4M 

// TOTAL is 3 Sqrt + 18M + 1S + 1I



