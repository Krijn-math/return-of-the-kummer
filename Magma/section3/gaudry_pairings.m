/*
  In this file we compute pairings using the first method (method (a) given in Section 3 of the accompanying paper)
  For this, we re-use part of Gaudry's amazing code (accompanying eprint/2005/314)
*/


if assigned is_main_script then
    filename := "file_loader.m";
    Write(filename, "\n" : Overwrite := true);
else
    is_main_script := true;
    print "gaudry_pairings.m is being executed directly.";
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

//load "../section2/general.m"; 
//load "../section3/gaudry_code.m";

// the below is outdated and superseded by the approaches in other files
// they show how the pairings are derived under the hood, but are not used anymore in subsequent files
// they may contain bugs and should not be used


function CheckIfRightGaudry(P, K, JP)
    //checks if a point P on fast kummer K actually maps back to JP
    t := ComputeThetaConstants(K);
    T := ThetaFromFundamentals(P, t);
    a := UfromZ(P, K, T, t);
    return a eq JP[1];
end function;

// now we should try to use this to get the neater pairing
// get the right value as in derive.m and then find the formulas
// for u0 and u1 in terms of X1 : .. : X4 as from UfromZ

function FirstTryFastPairing(P, K)
    //this should be the two tate pairing with (w3, w4) = (1, lambda)
    assert OnKummer(P, K);
    t := ComputeThetaConstants(K);
    T := ThetaFromFundamentals(P, t);
    a, b, c, d := Explode(K[2]);

    A := T[1]/a - T[3]/c;
    B := T[2]/b - T[4]/d;
    u0, u1, l, m, n := U0U1(P, K, T, t);

    res := (((A + B)^2*u0 - A*B*u1^2) * (1 - l)^2) / (A + B)^2;
    return res;
end function;

function FirstTryFastPairing2(P, K)
    //this should be the two tate pairing with (w3, w4) = (1, lambda)
    assert OnKummer(P, K);
    t := ComputeThetaConstants(K);
    T := ThetaFromFundamentals(P, t);
    a, b, c, d := Explode(K[2]);

    u0, u1, l, m, n := U0U1(P, K, T, t);

    wi := 1;
    wj := l;
    res := (wj^2 + u1*wj + u0)*(wi^2 + u1*wi + u0);
    return res;
end function;

function SecondTryFastPairing(P, K)
    //this should be the two tate pairing with (w5, w6) = (mu, nu)
    assert OnKummer(P, K);
    t := ComputeThetaConstants(K);
    T := ThetaFromFundamentals(P, t);
    a, b, c, d := Explode(K[2]);

    A := T[1]/a - T[4]/d;
    B := T[2]/b - T[3]/c;
    u0, u1, l, m, n := U0U1(P, K, T, t);
    res := ((A + B)^2*u0 - A*B*u1^2)  * (m - n)^2 / ((A + B)^2 );
    return res;
end function;

function Checker(arr, i, j, P, K)
    assert OnKummer(P, K);
    t := ComputeThetaConstants(K);
    T := ThetaFromFundamentals(P, t);
    i1, i2, i3, i4 := Explode(arr);

    A := T[i1]/t[i1] - T[i3]/t[i3];
    B := T[i2]/t[i2] - T[i4]/t[i4];
    u0, u1, l, m, n := U0U1(P, K, T, t);
    w := [0, 0, 1, l, m, n];
    if (A + B) eq 0 then return false; end if;
    return true;
end function;

function FastPairing_old(arr, i, j, P, K)
    //this should be the generalized two tate pairing
    assert OnKummer(P, K);
    t := ComputeThetaConstants(K);
    T := ThetaFromFundamentals(P, t);
    i1, i2, i3, i4 := Explode(arr);

    A := T[i1]/t[i1] - T[i3]/t[i3];
    B := T[i2]/t[i2] - T[i4]/t[i4];
    u0, u1, l, m, n := U0U1(P, K, T, t);
    w := [0, 0, 1, l, m, n];
    res := ((A + B)^2*u0 - A*B*u1^2)  * (w[i] - w[j])^2 / ((A + B)^2 );
    return res;
end function;

function FastTwoPairingUnderTheHood_old(arr, i, j, P, K)
    //this should be the generalized two tate pairing
    assert OnKummer(P, K);
    t := ComputeThetaConstants(K);
    T := ThetaFromFundamentals(P, t);
    a, b, c, d := Explode(K[2]);
    l := a*c/(b*d);

    U0 := l*T[14]*t[8]/(T[16]*t[10]);   //we should be able to shave these denom of i think
    U1 := (l-1)*T[13]*t[5]/(T[16]*t[10]);
    u0 := U0;
    u1 := (U1-U0-1);

    i1, i2, i3, i4 := Explode(arr);
    A := T[i1]/t[i1] - T[i3]/t[i3];
    B := T[i2]/t[i2] - T[i4]/t[i4];

    res := ((A + B)^2*u0 - A*B*u1^2); //squares removed, can we simplify more?
    return res;
end function;

//the other pairing, say with w2 = 0 and w3 = 1 should be
//u0*(u0 + u1 + 1) = U0*U1 = 
//  U0 := l*T[14]*t[8]/(T[16]*t[10]);
//  U1 := -(1-l)*T[13]*t[5]/(T[16]*t[10]);
//so we can skip the denominator (its a square)
//and simply use l*(l-1)*T[13]*T[14]*t[5]*t[8]
// with l := t[1]*t[3]/(t[2]*t[4]) i.e. ac/bd

function LastPairing(P, K)
    assert OnKummer(P, K);
    t := ComputeThetaConstants(K); 
    //we really only need t[8] and t[10] aka e, f
    //we can get e/f from a, b, c, d using the dual theta's
    //which is enough to get m and n
    
    X1, X2, X3, X4 := Explode(P);

    T := ThetaFromFundamentals(P, t);   //only need this for the redundant denom
    // u0, u1, l, m, n := U0U1(P, K, T, t);
    //U0, U1 := U0U1_last(P, K, T, t);

    T13 := ( -t[8]*t[9]*X1  + t[9]*t[10]*X2 + t[7]*t[8]*X3  - t[7]*t[10]*X4 ) / (t[7]^2-t[9]^2);
    T14 := ( -t[5]*t[9]*X1  - t[6]*t[7]*X2  + t[5]*t[7]*X3  + t[6]*t[9]*X4  ) / (t[7]^2-t[9]^2);

    lambda := t[1]*t[3]/(t[2]*t[4]);
    res := lambda*(lambda-1)*T13*T14*t[5]*t[8]   /   (T[16]*t[10])^2;
    return res; //notice we can remove some squares here still
end function;



function FastTwoPairing(i, j, P, K)
    //this should be the generalized two tate pairing
    assert OnKummer(P, K);

    if i eq 1 or j eq 1 then
      rest := [ k : k in [1..6] | k ne i and k ne j];
      i2, j2, i3, j3 := Explode(rest);
      return FastTwoPairing(i2, j2, P, K)*FastTwoPairing(i3, j3, P, K);
    end if;

    t := ComputeThetaConstants(K);
    a, b, c, d := Explode(K[2]);

    // we need lambda in u0 anyway
    l := a*c/(b*d);
    m := 0; n:= 0; //will be updated if needed
    // we need the other two (and thus t[8] and t[10]) if we have either 5 or 6

    if i gt 4 or j gt 4 then
      e := t[8]; f := t[10];
      m := a*e/(b*f);
      n := c*e/(d*f);   
    end if;

    w := [0, 0, 1, l, m, n];

    //this part we seem to need anyway, but the squares probably not
    X1, X2, X3, X4 := Explode(P);
    T13 := ( -t[8]*t[9]*X1  + t[9]*t[10]*X2 + t[7]*t[8]*X3  - t[7]*t[10]*X4 ) / (t[7]^2-t[9]^2);
    T14 := ( -t[5]*t[9]*X1  - t[6]*t[7]*X2  + t[5]*t[7]*X3  + t[6]*t[9]*X4  ) / (t[7]^2-t[9]^2);
    T16 := ( -t[6]*t[7]*X1  - t[5]*t[9]*X2  + t[6]*t[9]*X3  + t[5]*t[7]*X4 )  / (t[7]^2-t[9]^2);

    //bug hunting, doesnt happen often
    if T16 eq 0 or t[10] eq 0 then <T16, t[10]>; end if;

    //idea: we only need t[8]/t[10] here which is e/f which is easier to compute from l, m, n
    U0 := l*T14*t[8]/(T16*t[10]);   //we should be able to shave these denom of i think
    U1 := (l-1)*T13*t[5]/(T16*t[10]);
    u0 := U0;
    u1 := (U1-U0-1);

    wi := w[i]; wj := w[j];
    res := (wi^2 + u1*wi + u0)*(wj^2 + u1*wj + u0);
    if res eq 0 then
        //this is the case where on the jac the GCD is not 1, so we get one of the two
        //resultants evaluating to zero
        //so we should be able to detect this case, somehow? and then add a point S, then 
        //take pairing P+S and subtract pairing in S, but is going to be non-deterministic
        assert false;
    end if;
    return Fp!res;
end function;


////////////////////////////////////////////////////////
////////////////////////////////////////////////////////
/////////////////      TESTING        //////////////////
////////////////////////////////////////////////////////
////////////////////////////////////////////////////////

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
    b := FastTwoPairing(3,4, Pfast, K_fast2);
    if a ne b then 
      //probably happens in the "special" cases where gcd ne 1
      "error report:";
      "i is: ", i;
      "L34J is: ", L34J;
      "P on Jac is: ", P;
      "P on Kummer is: ", Pfast;
    end if;
    assert a eq b;
end for;

"jac pairing compared to FastTwo34";

//this is the point matching up to (w5 w6);
L56J := J_ros2![(x - w5)*(x - w6), 0];
L56fast2 := RosenhainToKummer(L56J, ros2, K_fast2);  

for i in [1..10] do
    repeat 
      P := Random(J_ros2);
      Pfast := RosenhainToKummer(P, ros2, K_fast2);  
    until GCD(P[1], L56J[1]) eq 1 and Pfast ne [0,0,0,0];    
    assert jacTwoTatePairing(L56J, P) eq FastTwoPairing(5, 6, Pfast, K_fast2);
end for;

"jac pairing compared to FastTwo56";

//this is the point matching up to (w2, w3);
L23 := J_ros2![(x - 0)*(x - 1), 0];
L23fast := RosenhainToKummer(L23, ros2, K_fast2);   //this doesnt work!!!

for i in [1..10] do
    repeat 
      P := Random(J_ros2);
      Pfast := RosenhainToKummer(P, ros2, K_fast2);  
    until GCD(P[1], L23[1]) eq 1 and Pfast ne [0,0,0,0];   
    a := jacTwoTatePairing(L23, P);
    b := FastTwoPairing(2, 3, Pfast, K_fast2);
    assert a eq b;
end for;

"jac pairing compared to FastTwo23";
"pairings work";
"loading gaudry done\n\n";