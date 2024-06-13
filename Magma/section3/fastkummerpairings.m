/*
  Computing pairings on Kummer surfaces
  Here we use method (b) described in Section 3 of the accompanying paper
*/

// We re-use part of Gaudry's amazing code, used in (2005/314)

if assigned is_main_script then
    filename := "file_loader.m";
    Write(filename, "\n" : Overwrite := true);
else
    is_main_script := true;
    print "fastkummerpairings.m is being executed directly.";
    filename := "file_loader.m";

    files := [
        "../costello-code/Params.m",
        "../costello-code/Kummer.m",
        "../costello-code/Maps.m",
        "../section2/invariants.m",
        "../section2/more_maps.m",
        "../section2/general.m",
        "../section3/gaudry_code.m"
        ];
    Write(filename, "\n" : Overwrite := true);
    for file in files do
        tmp :=  "load '" cat file cat "'; \n"; 
        Write(filename, tmp);
    end for;
end if;
load "file_loader.m";

// load "../section2/general.m"; 
// load "../section3/gaudry_code.m";

function FastTwoPairing(pair, P, K)
    // we compute the tate pairing value for pair = <i,j>
    // using theta coordinates to ensure the same result as the Jacobian pairing
    // corresponding to Method 1 from Section 3.3
    // Note: seems to contain a small bug, and in terms of cost we prefer Method 2 (Robert) or Method 3 (v2)
    // these can be found in robert_pairings.m and v2_and_new_pairings.m

    assert OnKummer(P, K);
    i := pair[1];
    j := pair[2];

    if i eq 1 or j eq 1 then
      //infinity pairing can be done with two other pairings
      rest := [ k : k in [1..6] | k ne i and k ne j];
      i2, j2, i3, j3 := Explode(rest);
      return FastTwoPairing(<i2, j2>, P, K)*FastTwoPairing(<i3, j3>, P, K);
    end if;

    t := ComputeThetaConstants(K);
    a, b, c, d := Explode(K[2]);

    // we need lambda in u0
    l := a*c/(b*d);
    m := 0; n:= 0; //will be updated if needed in lines 79, 80
    // we need the other two (and thus t[8] and t[10]) if we have either 5 or 6

    if i gt 4 or j gt 4 then
      e := t[8]; f := t[10];
      m := a*e/(b*f);
      n := c*e/(d*f);   
    end if;

    w := [0, 0, 1, l, m, n];

    //this part we need, but the squares probably not, because we want to compute the reduced 2-pairing
    //hence the squares do not impact the result
    X1, X2, X3, X4 := Explode(P);
    T13 := ( -t[8]*t[9]*X1  + t[9]*t[10]*X2 + t[7]*t[8]*X3  - t[7]*t[10]*X4 ) / (t[7]^2-t[9]^2);
    T14 := ( -t[5]*t[9]*X1  - t[6]*t[7]*X2  + t[5]*t[7]*X3  + t[6]*t[9]*X4  ) / (t[7]^2-t[9]^2);
    T16 := ( -t[6]*t[7]*X1  - t[5]*t[9]*X2  + t[6]*t[9]*X3  + t[5]*t[7]*X4 )  / (t[7]^2-t[9]^2);

    //we only need t[8]/t[10] here which is e/f which is easier to compute from l, m, n
    U0 := l*T14*t[8]/(T16*t[10]);  
    U1 := (l-1)*T13*t[5]/(T16*t[10]);
    u0 := U0;
    u1 := (U1-U0-1);

    wi := w[i]; wj := w[j];
    res := (wi^2 + u1*wi + u0)*(wj^2 + u1*wj + u0);
    return Fp!res;
end function;

function Profile(P, K)
  //uses the above pairing to compute the 2-profile of P on K
  assert OnKummer(P, K);

  return < IsSquare(FastTwoPairing(<i, j>, P, K)) select 1 else -1 : i,j in [1..6] | i lt j >;
end function;

function SmallProfile(P, K)
  // uses the above pairing to compute the 2-profile of P on K
  // here small refer to indices that give a basis of the 2-torsion
  // hence the smaller profile for this basis still contains al the information we need
  // by bilinearity of the Tate pairing
  assert OnKummer(P, K);
  small := [<2, 3>, <2, 4>, <2, 5>, <2, 6>];
  return < IsSquare(FastTwoPairing(pair, P, K)) select 1 else -1 : pair in small>;
end function;

///////////////////////////////////////////
///////////////////////////////////////////
///////////////////////////////////////////
//////////////   TESTING   ////////////////
///////////////////////////////////////////
///////////////////////////////////////////

w3, w4, w5, w6 := Explode([1] cat ros2);
//this is the point matching up to (w3, w4);
L34J := J_ros2![(x - w3)*(x - w4), 0];
L34fast2 := RosenhainToKummer(L34J, ros2, K_fast2);  

for i in [1..10] do
    repeat 
      P := Random(J_ros2);
      Pfast := RosenhainToKummer(P, ros2, K_fast2);  
    until GCD(P[1], L34J[1]) eq 1 and Pfast ne [0,0,0,0];
    a := jacTwoTatePairing(L34J, P);
    b := FastTwoPairing(<3, 4>, Pfast, K_fast2);
    if a ne b then 
      "error report:";
      "i is: ", i;
      "L34J is: ", L34J;
      "P on Jac is: ", P;
      "P on Kummer is: ", Pfast;
    end if;
    assert a eq b;
end for;

//this is the point matching up to (w5 w6);
L56J := J_ros2![(x - w5)*(x - w6), 0];
L56fast2 := RosenhainToKummer(L56J, ros2, K_fast2);  

for i in [1..10] do
    repeat 
      P := Random(J_ros2);
      Pfast := RosenhainToKummer(P, ros2, K_fast2);  
    until GCD(P[1], L56J[1]) eq 1 and Pfast ne [0,0,0,0];   
    assert jacTwoTatePairing(L56J, P) eq FastTwoPairing(<5, 6>, Pfast, K_fast2);
end for;

//this is the point matching up to (w2, w3);
L23 := J_ros2![(x - 0)*(x - 1), 0];
L23fast := RosenhainToKummer(L23, ros2, K_fast2);   //this doesnt work!!!

for i in [1..10] do
    repeat 
      P := Random(J_ros2);
      Pfast := RosenhainToKummer(P, ros2, K_fast2);  
    until GCD(P[1], L23[1]) eq 1 and Pfast ne [0,0,0,0];   
    assert jacTwoTatePairing(L23, P) eq FastTwoPairing(<2, 3>, Pfast, K_fast2);
end for;
"pairings work";

///////////////////////////////////////////
///////////////////////////////////////////
//////////////   PROFILE   ////////////////
///////////////////////////////////////////
///////////////////////////////////////////

// the approach below was later on improved in elegant_sampling.m
// it may still contain bugs, but remains here for explaining the ideas a bit more

function RosenhainBasis(ros)
  // returns the two torsion points on the Jacobian of some Rosenhain values
  w := [0, 0, 1] cat ros;
  J := Jacobian(HyperellipticCurve(&*[x - w[i] : i in [2..6]]));
  J := BaseChange(J, Fp);
  Ltwo := [J![(x - w[i])*(x-w[j]),0] : i,j in [2..6] | i lt j];
  Ltwo := Ltwo cat [J![(x - w[i]),0] : i in [2..6]]; 

  return Ltwo;
end function;

Ltwo := RosenhainBasis(ros);
SmallL := Ltwo[1..4];

function jacProfile(D)
  // computes the profile of an element D in Jac using the Jacobian pairings
    return < IsSquare(jacTwoTatePairing(L, D)) select 1 else -1 : L in SmallL >;
end function;

// but we should also be able to get all the eta(E_alpha) + a*P3 + b*P4 
// and then simply remove that part to greatly improve our odds

// we do so by first picking the right basis on J_rosenhain
// then we can find the profiles on K that are "bad", e.g. they correspond
// to points of non-full order + P3 or P4

// these will immediately be in the image of eta(E_alpha)
GoodProfiles := { 
  <-1, 1, -1, 1>, 
  <1, -1, 1, -1>, 
  <-1, -1, -1, -1>
};

// these are the bad bases, e.g. their points do not contain a 2^f2 torsion part
BadProfiles := {
  <-1, -1, 1, 1>,
  <-1, -1, 1, 1>,
  <-1, -1, -1, 1>,
  <1, 1, 1, 1>
};

// what this means is if we sample a point and it's in GoodProfiles, we are done!
// if its not in badprofiles, we can add a two torsion point

i := 0;
repeat repeat i +:= 1; T, P := SpecificKummerPoint(K, [1, 2, i, 0]); until T; 
until SmallProfile(P, K) notin BadProfiles;


// to improve this, we should sample not points randomly, but with specific values 
// so that we are sure to get some good part of the profile already

// I want to use the fact that u0 and u1 completely determine the profile of P
// and so if u0 and u1 are okay with respect to the curve then can we find the suitable v0?
// what if we keep it as an unknown in the polynomial until we find a root

function FirstTry(u)
  u1 := -2;
  u0 := u;

  f := x^2 + u1*x + u0;
  return IsSquare(Fp!Resultant(HyperellipticPolynomials(C_alpha), f));
end function;

function SecondTry(u)
  u1 := -2;
  u0 := u;

  poly<T> := PolynomialRing(Fp);
  a, b, c, d := Explode(K[2]);
  w := [0, 0, 1] cat ros;
  w1, w2, w3, w4, w5, w6 := Explode(w);
  x  := a*(u0*(w3*w5 - u0)*(w4 + w6 + u1) - T^2);
  y  := b*(u0*(w4*w6 - u0)*(w3 + w5 + u1) - T^2);
  z  := c*(u0*(w3*w6 - u0)*(w4 + w5 + u1) - T^2);
  t  := d*(u0*(w4*w5 - u0)*(w3 + w6 + u1) - T^2);
  Eq := K[1][1]*(x*y*z*t)-((x^2+y^2+z^2+t^2)-K[1][2]*(x+y)*(z+t)-K[1][3]*(x*y+z*t))^2;
  return HasRoot(Eq);
end function;

function Construct(pair)
  u, v := Explode(pair);
  u1 := -2;
  u0 := u;
  a, b, c, d := Explode(K[2]);
  w := [0, 0, 1] cat ros;
  w1, w2, w3, w4, w5, w6 := Explode(w);
  x  := a*(u0*(w3*w5 - u0)*(w4 + w6 + u1) - v^2);
  y  := b*(u0*(w4*w6 - u0)*(w3 + w5 + u1) - v^2);
  z  := c*(u0*(w3*w6 - u0)*(w4 + w5 + u1) - v^2);
  t  := d*(u0*(w4*w5 - u0)*(w3 + w6 + u1) - v^2);
  P := [x, y, z, t];
  assert OnKummer(P, K);
  return P;
end function;

// nonsquares
U := [ 7, 13, 17, 21, 26, 28, 31, 34, 37, 39, 42, 47, 51, 56, 62, 65, 67, 70, 73, 77 ];
// after first try
U2 := [u : u in U | FirstTry(u)];

// find pairs
sols := [];
for u in U2 do t, r := SecondTry(u); if t then Append(~sols, <u, r>); end if; end for;
testPoints := [ Construct(p) : p in sols ];

"fastkummerpairing.m done\n\n";
