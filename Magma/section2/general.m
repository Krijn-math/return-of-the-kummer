/*
    This is a relatively complicated file, containing mostly containing functionality for the general 
    kummer surface, which exists as an object in Magma unlike the squared kummer surface
*/

if assigned is_main_script then
    filename := "file_loader.m";
    Write(filename, "\n" : Overwrite := true);
else
    is_main_script := true;
    print "general.m is being executed directly.";
    filename := "file_loader.m";

    files := [
        "../costello-code/Params.m",
        "../costello-code/Kummer.m",
        "../costello-code/Maps.m",
        "../section2/invariants.m",
        "../section2/more_maps.m"
        ];
    Write(filename, "\n" : Overwrite := true);
    for file in files do
        tmp :=  "load '" cat file cat "'; \n"; 
        Write(filename, tmp);
    end for;
end if;
load "file_loader.m";
//load "../section2/more_maps.m";

poly<x1, x2, x3, x4> := PolynomialRing(Fp, 4);

///////////////////////////////////////////////////////////////
////////////////////// RANDOM POINTS //////////////////////////
///////////////////////////////////////////////////////////////


function Krandom(K)
    //for some reason, you cannot use Random on K in magma, but this works
    //note: not a uniform distribution as points of order 2 are only half as likely
    //but good enough for what we want
    return K!Random(Parent(K));
end function;

function RandomGeneralKummerPoint(kummer)
    //samples a random point on the Kummer by sampling a random point on the Jacobian above and mapping down
    jac := Jacobian(kummer);
    repeat
    D := Random(jac);
    try
        res := kummer!D; a := 1;
    catch e
        //there is a strange magma bug that happens sometimes
        a := 0;
        "this happens";
    end try;
    until a eq 1;
    return res;
end function;


///////////////////////////////////////////////////////////////
///////////////////// TWO-TORSION POINTS //////////////////////
///////////////////////////////////////////////////////////////

function JacHyp_getAllTwoTorsion(jac)
    //helper function to get the two torsion on the jacobian
    //easier to do by simply using the weierstrass values
    //e.g. factor the defining polynomial

    G, phi := TwoTorsionSubgroup(jac);
    return [phi(g) : g in G | not IsZero(phi(g))];
end function;


function Kgen_getAllTwoTorsion(Kgen)
    //assuming a general kummer surface K of a curve in the form y^2 = f(x)
    //finds all the two torsion K by the simple map given by the roots of the defining polynomial

    rhs := HyperellipticPolynomials(Curve(Jacobian(Kgen)));
    wp := [ p[1] : p in Roots(rhs)];
    if #wp lt 5 then
        //todo: solve by extension field
        done := false;
        assert done;
    end if;

    Points := [];
    for i in [1..#wp-1] do
    for j in [i+1..#wp] do
        a := wp[i];
        b := wp[j];
        c := Roots(UnivariatePolynomial(Evaluate(DefiningPolynomial(Kgen), <1, a+b, a*b, x4>)))[1][1];
        point := Kgen![1, a + b, a*b, c];
        assert 2*point eq 0*point;
        Append(~Points, point);
    end for;
    end for;

    //if infinity is a weierstrass point, add the (0 : 1 : x : x^2) points
    if #wp eq 5 then
        for x in wp do
            point := Kgen![0, 1, x, x^2];
            assert 2*point eq 0*point;
            Append(~Points, point);
        end for;
    end if;

    assert #Points eq 15;
    return Points;
end function;

function GetAllTwoTorsion(KgenORJac)
    //helper function that combines the two functions above based on the Type of the object
    if Type(KgenORJac) eq SrfKum then
        return Kgen_getAllTwoTorsion(KgenORJac);
    end if;

    if Type(KgenORJac) eq JacHyp then
        return JacHyp_getAllTwoTorsion(KgenORJac);
    end if;

    return "unknown type";
end function;

function getW(K1)
    //the maps W_ij from Cassels & Flynn for addition by a point of order 2
    //uses the formulas given in 3.2.10a
    K := Parent(K1);
    assert 2*K1 eq K!0;

    f := HyperellipticPolynomials(Curve(Jacobian(K)));
    T := Parent(f).1;
    g := T^2 - K1[2]*T + K1[3];
    h := f div g;
    g0, g1, g2 := Explode(Coefficients(g));
    assert g2 eq 1;

    if #Coefficients(h) eq 5 then
        h0, h1, h2, h3, h4 := Explode(Coefficients(h));
        assert h4 eq Coefficients(f)[7];
    else
        H := Coefficients(h); repeat H := H cat [0]; until #H eq 5;
        h0, h1, h2, h3, h4 := Explode(H);
    end if;

    w41 := -g1*g2^2*h0*h1 + g1^2*g2*h0*h2 + g0*g2^2*h1^2 - 4*g0*g2^2*h0*h2
            - g0*g1*g2*h1*h2 + g0*g1*g2*h0*h3 - g0^2*g2*h1*h3;
    w42 := g1^2*g2*h0*h3 - g1^3*h0*h4 - 2*g0*g2^2*h0*h3 - g0*g1*g2*h1*h3
           + 4*g0*g1*g2*h0*h4 + g0*g1^2*h1*h4 - 2*g0^2*g2*h1*h4;
    w43 := -g0*g2^2*h1*h3 - g0*g1*g2*h2*h3 + g0*g1*g2*h1*h4 + g0*g1^2*h2*h4
           +g0^2*g2*h3^2 - 4*g0^2*g2*h2*h4 - g0^2*g1*h3*h4;
    w44 := -g2^2*h0 - g0*g2*h2 - g0^2*h4;

    W := Matrix([
        [g2^2*h0 + g0*g2*h2 - g0^2*h4, g0*g2*h3 - g0*g1*h4, g1*g2*h3 - g1^2*h4 + 2*g0*g2*h4, g2],
        [-g0*g2*h1 - g0*g1*h2 + g0^2*h3, g2^2*h0 - g0*g2*h2 + g0^2*h4, g2^2*h1 - g1*g2*h2 - g0*g2*h3, -g1],
        [-g1^2*h0 + 2*g0*g2*h0 + g0*g1*h1, -g1*g2*h0 + g0*g2*h1, -g2^2*h0 + g0*g2*h2 + g0^2*h4, g0],
        [w41, w42, w43, w44]
    ]);

    assert W^2/(W^2)[1][1] eq 1;
    return W;
end function;

function AddTwo(K1, K2)
    //given two points on K where K1 is of order 2, we can use the map W_ij
    //then return W_ij applied to K2
    K := Parent(K1);
    assert K eq Parent(K2);

    W := getW(K1);
    return K!Eltseq(Transpose(W*Transpose(Matrix([Eltseq(K2)]))));
end function;


function aboveTwo(Jpoint)
    //checks the weierstrass values that the Jpoint of order 2 is from
    //could probably be done easier

    if IsOdd(Order(Jpoint)) then
        return "Not above two";
    end if;

    //get the weierstrass coords
    wp := [* p[1] : p in Roots(HyperellipticPolynomials(Curve(Parent(Jpoint)))) *];

    if #wp eq 5 then
        wp := [* "inf" *] cat wp;
    end if;

    //these should be weierstrass
    Jtwox := [p[1] : p in Roots(((Order(Jpoint) div 2)*Jpoint)[1])];
    if #Jtwox eq 2 then
        //nice case, go on
        res1 := Index(wp, Jtwox[1]);
        res2 := Index(wp, Jtwox[2]);
        return <res1, res2>;
    end if;
    
    //inf is in there
    res1 := wp[1];
    res2 := Index(wp, Jtwox[1]);
    return [* res1, res2 *];
end function;

///////////////////////////////////////////////////////////////
//////////// EQUATIONS FOR GENERAL KUMMER SURFACE /////////////
///////////////////////////////////////////////////////////////


function MyDefPol(curve)
    //uses the formulas given by Cassels & Flynn to compute the 
    //defining equations of the general Kummer surface given a hyperelliptic curve
    f := Coefficients(HyperellipticPolynomials(curve));
    if #f eq 6 then f[7] := 0; end if;
    f0, f1, f2, f3, f4, f5, f6 := Explode(f);


    k1 := x1;
    k2 := x2;
    k3 := x3;
    k4 := x4;

    K2 := k2^2 - 4*k1*k3;
    K1 := -4*k1^3*f0 - 2*k1^2*k2*f1 -4*k1^2*k3*f2 - 2*k1*k2*k3*f3 -4*k1*k3^2*f4
        -2*k2*k3^2*f5 - 4*k3^3*f6;

    K0 := -4*k1^4*f0*f2 + k1^4*f1^2 - 4*k1^3*k2*f0*f3 - 2*k1^3*k3*f1*f3 - 4*k1^2*k2^2*f0*f4
        +4*k1^2*k2*k3*f0*f5 - 4*k1^2*k2*k3*f1*f4 - 4*k1^2*k3^2*f0*f6 + 2*k1^2*k3^2*f1*f5
        -4*k1^2*k3^2*f2*f4 + k1^2*k3^2*f3^2 - 4*k1*k2^3*f0*f5 + 8*k1*k2^2*k3*f0*f6
        -4*k1*k2^2*k3*f1*f5 + 4*k1*k2*k3^2*f1*f6 - 4*k1*k2*k3^2*f2*f5
        -2*k1*k3^3*f3*f5 - 4*k2^4*f0*f6 - 4*k2^3*k3*f1*f6 - 4*k2^2*k3^2*f2*f6
        -4*k2*k3^3*f3*f6 - 4*k3^4*f4*f6 + k3^4*f5^2;

    Kall := K2*k4^2 + K1*k4 + K0;
    return Kall;
end function;


function getKforKummers(K)
    //given a general kummer surface, computes the defining polynomials K0, K1 and K2
    f := DefiningPolynomial(K); rest := f; pol := Parent(rest);
    x1 := pol.1;
    x2 := pol.2;
    x3 := pol.3;
    x4 := pol.4;
    K0 := Evaluate(rest, <x1, x2, x3, 0>);
    rest := (rest - K0) div x4;
    K1 := Evaluate(rest, <x1, x2, x3, 0>);
    K2 := (rest - K1) div x4;
    assert f eq K0 + x4*K1 + x4^2*K2;
    return K0, K1, K2;
end function;


///////////////////////////////////////////////////////////////
///////////////////// HELPER FUNCTIONS ////////////////////////
///////////////////////////////////////////////////////////////


function newCoeff(kappa, old_coeff)
    //returns the coefficients of the curve C' after applying kappa
    //that is, kappa is a mobius transform C --> C' in terms of a, b, c, d, e
    //then given c0, c1, c2, c3, c4, c5, c6 as coefficients of the RHS of C
    //this function returns the coefficients of the RHS of C'

    //WARNING: only works for the degree 6 model!
    a, b, c, d, e := Explode(kappa[1]);
    c0, c1, c2, c3, c4, c5, c6 := Explode(old_coeff);

    newc0 := (a^6*c0 - a^5*b*c1 + a^4*b^2*c2 - a^3*b^3*c3 + a^2*b^4*c4 - a*b^5*c5 +
        b^6*c6);

    newc1 := (-6*a^5*c*c0 +
        a^5*d*c1 + 5*a^4*b*c*c1 - 2*a^4*b*d*c2 - 4*a^3*b^2*c*c2 + 3*a^3*b^2*d*c3 +
        3*a^2*b^3*c*c3 - 4*a^2*b^3*d*c4 - 2*a*b^4*c*c4 + 5*a*b^4*d*c5 + b^5*c*c5 -
        6*b^5*d*c6);

    newc2 := (15*a^4*c^2*c0 - 5*a^4*c*d*c1 + a^4*d^2*c2 -
        10*a^3*b*c^2*c1 + 8*a^3*b*c*d*c2 - 3*a^3*b*d^2*c3 + 6*a^2*b^2*c^2*c2 -
        9*a^2*b^2*c*d*c3 + 6*a^2*b^2*d^2*c4 - 3*a*b^3*c^2*c3 + 8*a*b^3*c*d*c4 -
        10*a*b^3*d^2*c5 + b^4*c^2*c4 - 5*b^4*c*d*c5 + 15*b^4*d^2*c6);

    newc3 := (-20*a^3*c^3*c0 + 10*a^3*c^2*d*c1 -
        4*a^3*c*d^2*c2 + a^3*d^3*c3 + 10*a^2*b*c^3*c1 - 12*a^2*b*c^2*d*c2 +
        9*a^2*b*c*d^2*c3 - 4*a^2*b*d^3*c4 - 4*a*b^2*c^3*c2 + 9*a*b^2*c^2*d*c3 -
        12*a*b^2*c*d^2*c4 + 10*a*b^2*d^3*c5 + b^3*c^3*c3 - 4*b^3*c^2*d*c4 + 10*b^3*c*d^2*c5
        - 20*b^3*d^3*c6);

    newc4 := (15*a^2*c^4*c0 - 10*a^2*c^3*d*c1 + 6*a^2*c^2*d^2*c2 -
        3*a^2*c*d^3*c3 + a^2*d^4*c4 - 5*a*b*c^4*c1 + 8*a*b*c^3*d*c2 - 9*a*b*c^2*d^2*c3 +
        8*a*b*c*d^3*c4 - 5*a*b*d^4*c5 + b^2*c^4*c2 - 3*b^2*c^3*d*c3 + 6*b^2*c^2*d^2*c4 -
        10*b^2*c*d^3*c5 + 15*b^2*d^4*c6);

    newc5 := (-6*a*c^5*c0 + 5*a*c^4*d*c1 - 4*a*c^3*d^2*c2 + 3*a*c^2*d^3*c3 - 2*a*c*d^4*c4 +
        a*d^5*c5 + b*c^5*c1 - 2*b*c^4*d*c2 + 3*b*c^3*d^2*c3 - 4*b*c^2*d^3*c4 + 5*b*c*d^4*c5
        - 6*b*d^5*c6);

    newc6 := (c^6*c0 - c^5*d*c1 + c^4*d^2*c2 - c^3*d^3*c3 + c^2*d^4*c4 - c*d^5*c5 + d^6*c6);

    newy := (-a^6*d^6 + 6*a^5*b*c*d^5 - 15*a^4*b^2*c^2*d^4 + 20*a^3*b^3*c^3*d^3 -
        15*a^2*b^4*c^4*d^2 + 6*a*b^5*c^5*d - b^6*c^6)/e^2;

    return [newc0/-newy, newc1/-newy, newc2/-newy, newc3/-newy, newc4/-newy, newc5/-newy, newc6/-newy ];

end function;

function getCoeff(K)
    //given the defining polynomials for a general kummer K
    //the following formulas allow us to find the coefficients of the overlying curve C

    K0, K1, K2 := getKforKummers(K);
    x1 := Parent(K1).1;
    x2 := Parent(K1).2;
    x3 := Parent(K1).3;
    x4 := Parent(K1).4;

    c0 := MonomialCoefficient(K1, x1^3)/(-4);
    c1 := MonomialCoefficient(K1, x1*x2*x1)/(-2);
    c2 := MonomialCoefficient(K1, x1*x1*x3)/(-4);
    c3 := MonomialCoefficient(K1, x1*x2*x3)/(-2);
    c4 := MonomialCoefficient(K1, x1*x3*x3)/(-4);
    c5 := MonomialCoefficient(K1, x3*x2*x3)/(-2);
    c6 := MonomialCoefficient(K1, x3*x3*x3)/(-4);

    return [c0, c1, c2, c3, c4, c5, c6];
end function;


///////////////////////////////////////////////////////////////
///////// MAPS INVOLVING THE GENERAL KUMMER SURFACE ///////////
///////////////////////////////////////////////////////////////


function MapDown(P1, P2)
    //the explicit map down from the curve to the kummer
    //by mapping the x- and y-coordinates as described in 
    // Cassels & Flynn. 
    // Note that this functionality is simply in Magma to by coercion
    curve := Curve(P1);
    f := Coefficients(HyperellipticPolynomials(curve));
    if #f eq 6 then f[7] := 0; end if;
    f0 := f[1];
    f1 := f[2];
    f2 := f[3];
    f3 := f[4];
    f4 := f[5];
    f5 := f[6];
    f6 := f[7];

    pol<x,u> := PolynomialRing(Fp, 2);
    F0 := 2*f0 + f1*(x+u) + 2*f2*(x*u) + f3*(x+u)*x*u + 2*f4*(x*u)^2
        +f5*(x+u)*(x*u)^2 + 2*f6*(x*u)^3;

    xx := P1[1]; yy := P1[2]; uu := P2[1]; vv := P2[2];
    k1 := 1;
    k2 := xx + uu;
    k3 := xx*uu;
    k4 := ( Evaluate(F0, <xx,uu>) - 2*yy*vv )  /  (xx-uu)^2;

    return [k1,k2,k3,k4];
end function;

function MumMapDown(mumford)
    //the explicit map down from the curve to the kummer
    //by mapping mumford representation down as described in 
    // Cassels & Flynn. 
    // Note that this functionality is simply in Magma to by coercion
    jac := Parent(mumford);
    curve := Curve(jac);
    f := Coefficients(HyperellipticPolynomials(curve));
    if #f eq 6 then f[7] := 0; end if;
    f0 := f[1];
    f1 := f[2];
    f2 := f[3];
    f3 := f[4];
    f4 := f[5];
    f5 := f[6];
    f6 := f[7];

    coeffs1 := Coefficients(mumford[1]);
    coeffs2 := Coefficients(mumford[2]);
    k1 := 1;
    k2 := -coeffs1[2];
    k3 := coeffs1[1];
    if #coeffs2 eq 2 then
        alpha := coeffs2[2];
        beta := coeffs2[1];
    else
        alpha := 0;
        beta := coeffs2[1];
    end if;

    F0 := 2*f0 + f1*k2 + 2*f2*k3 + f3*k2*k3 + 2*f4*k3^2
        +f5*k2*k3^2 + 2*f6*k3^3;

    yv := alpha^2*k3 + alpha*beta*k2 + beta^2;
    xminu2 := k2^2 - 4*k3;

    //xminu2 is zero for "double" points D = 2(P) - D_inf
    //but magma can still map them to some sensical value...

    k4 := (F0 - 2*yv)/xminu2;
    return KummerSurface(jac)![k1, k2, k3, k4];
end function;


function evalKappastarstar2(point, kappa, Kend)
    //given a map kappa as a mobius transform between the hyperelliptic curves
    //this evaluates it as a map on the general kummer surfaces of those curves
    Kstart := Parent(point);
    a, b, c, d, e := Explode(kappa[1]);
    k := Eltseq(point);

    bot := c^2*k[3] + c*d*k[2] + d^2;
    kprime2 := (2*a*c*k[3] + (a*d + b*c)*k[2] + 2*b*d)/ bot;
    kprime3 := (a^2*k[3] + a*b*k[2] + b^2)/ bot;

    K0, K1, K2 := getKforKummers(Kstart);
    vv := -Evaluate(K1, <1, k[2], k[3], 1>) - 2*Evaluate(K2, <1, k[2], k[3], 1>)*k[4];
    vv := vv/4;

    K0p, K1p, K2p := getKforKummers(Kend);

    vvprime := e^2*vv / bot^3;
    F0prime := -Evaluate(K1p, <1, kprime2, kprime3, 1>)/2;
    kprime4 := (F0prime - 2*vvprime)/(kprime2^2 - 4*kprime3);
    return Kend![1, kprime2, kprime3, kprime4];
end function;

function codomainKappastarstar(K, kappa)
    //given a mobius transform kappa gives us the kummer surface of the codomain
    coeff_start := getCoeff(K);
    coeff_end := newCoeff(kappa, coeff_start);
    return KummerSurface(Jacobian(HyperellipticCurve(Reverse(coeff_end))));
end function;

function evalKappastarstar(point, kappa)
    //evaluates the induced map between kummer surfaces kappa** induced by a mobius transform kappa
    Kstart := Parent(point);
    Kend := codomainKappastarstar(Kstart, kappa);

    a, b, c, d,e := Explode(kappa[1]);
    k := Eltseq(point);

    bot := c^2*k[3] + c*d*k[2] + d^2;
    kprime2 := (2*a*c*k[3] + (a*d + b*c)*k[2] + 2*b*d)/ bot;
    kprime3 := (a^2*k[3] + a*b*k[2] + b^2)/ bot;

    K0, K1, K2 := getKforKummers(Kstart);
    vv := -Evaluate(K1, <1, k[2], k[3], 1>) - 2*Evaluate(K2, <1, k[2], k[3], 1>)*k[4];
    vv := vv/4;

    K0p, K1p, K2p := getKforKummers(Kend);

    vvprime := e^2*vv / bot^3;
    F0prime := -Evaluate(K1p, <1, kprime2, kprime3, 1>)/2;
    kprime4 := (F0prime - 2*vvprime)/(kprime2^2 - 4*kprime3);
    return Kend![1, kprime2, kprime3, kprime4];
end function;

///////////////////////////////////////////////////////////////
////////////////////////// PAIRINGS ///////////////////////////
///////////////////////////////////////////////////////////////

function curveTwoTatePairing(P1, P2, Q1, Q2)
    //given the x-values of two Weierstrass points P1 and P2
    //and given the x-values of two curve points Q1 and Q2
    //this function essentially represents the 2-tate pairing of D_P and D_Q
    //being their representations of elements of the Jacobian under C^(2) --> Jac
    assert P1[2] eq 0 and P2[2] eq 0;
    lambda := P1[1];
    mu := P2[1];
    u := Q1[1];
    up := Q2[1];

    return (u - lambda)*(u - mu)*(up - lambda)*(up - mu);
end function;

function special_jacTwoTatePairing(div1, div2)
    //for "special" divisors div1, div2 that are not coprime, 
    //we simply add a random divisor S until its no longer coprime
    //then compute the tate pairing as t(div1, div2) = t(div1, div2 + S)/t(div1, S)
    assert 2*div1 eq Parent(div1)![1,0];

    repeat S := Random(Parent(div1));
    until GCD(div1[1], (div2 + S)[1]) eq 1 and
          GCD(div1[1], S[1]) eq 1;

    a2 := div1[1];
    a := (div2 + S)[1];

    return Resultant(a2, a)/Resultant(a2, S[1]);
end function;

function jacTwoTatePairing(div1, div2)
    //given two divisors div1 and div2, computes the two tate pairing t(div1, div2)
    //using resultants

    assert 2*div1 eq Parent(div1)![1,0];
    a2 := div1[1];
    a := div2[1];

    if GCD(a2, a) ne 1  then
        return special_jacTwoTatePairing(div1, div2);
    end if;

    return Resultant(a2, a);
end function;

function jacTwoReducedTatePairing(div1, div2)
    //given two divisors div1 and div2, computes the reduced two tate pairing t(div1, div2)^(p^2 - 1)/2
    //using resultants

    assert 2*div1 eq Parent(div1)![1,0];
    return jacTwoTatePairing(div1, div2)^((p^2 - 1) div 2);
end function;

function check_share(kdiv1, kdiv2)
    //checks for coprimality of two elements of the kummer, corresponding of coprimality of their corresponding a(x)
    //polynomials in their Mumford representation
    k2 := kdiv1[2];
    k3 := kdiv1[3];
    l2 := kdiv2[2];
    l3 := kdiv2[3];

    res := k3^2 - l2*k2*k3
    + l2^2*k3 - l2*l3*k2 + l3^2
    +l3*(k2^2 - 2*k3);

    return res;
end function;

function special_kummerTwoTatePairing(kdiv1, kdiv2)
    //for two coprime elements, return an element T2 in K[2] that makes kdiv2 + T2
    //coprime with kdiv1 and T2 coprime with kdiv1
    twotors := GetAllTwoTorsion(Parent(kdiv1));
    i := 0;
    repeat i +:= 1; T2 := twotors[i];
    until check_share(kdiv1, AddTwo(T2, kdiv2)) ne 0
    and check_share(kdiv1, T2) ne 0;

    return T2;
end function;

function kummerTwoTatePairing(kdiv1, kdiv2)
    //computes the two tate pairing on the kummer using the formulas from section 3.3

    //WARNING: this probably computes the Tate pairing wrong if
    //either kdiv1 or kdiv2 is of the form (0 : 1 : k3 : k4)
    //or when they share a gcd, because it doesnt drop out (yet)


    assert 2*kdiv1 eq Parent(kdiv1)!0;

    //for now we assume normalisation, can be avoided
    assert kdiv1[1] eq 1;
    assert kdiv2[1] eq 1;


    k2 := kdiv1[2];
    k3 := kdiv1[3];
    l2 := kdiv2[2];
    l3 := kdiv2[3];

    res := k3^2 - l2*k2*k3
    + l2^2*k3 - l2*l3*k2 + l3^2
    +l3*(k2^2 - 2*k3);

    if res eq 0 then
        //either kdiv2 is of order 2 or not. If it is, just add a random point
        // this makes eval easy
        if 2*kdiv2 eq Parent(kdiv1)!0 then
            T := RandomGeneralKummerPoint(Parent(kdiv1));
            return kummerTwoTatePairing(kdiv1, AddTwo(kdiv2, T))/kummerTwoTatePairing(kdiv1, T);
        else
        //when it is not of order 2, just add a correct order two point
            T2 := special_kummerTwoTatePairing(kdiv1, kdiv2);
            return kummerTwoTatePairing(kdiv1, AddTwo(T2, kdiv2))/kummerTwoTatePairing(kdiv1, T2);
        end if;
    end if;

    return res;
end function;

//by using the map M we can also do two tate pairings on K^sqr
//but we prefer the other methods
function fastTwoTatePairing(L, P, K)
    assert DBL(L, K) eq K[2];
    ros := MuToRosenhain(K[2]);
    C_ros := HyperellipticCurve(x*(x-1)*(x-ros[1])*(x-ros[2])*(x-ros[3]));
    Kgen := KummerSurface(Jacobian(C_ros));
    M := M_kummer(ros, K[2]);      //between fast and gen

    //map points to the generic
    Lgen := Kgen!Eltseq(Matrix([L])*M);
    Pgen := Kgen!Eltseq(Matrix([P])*M);

    //compute pairing there
    return Fp!kummerTwoTatePairing(Lgen, Pgen);
end function;


///////////////////////////////////////////////////////////////
/////////////////////// JACOBIAN BASIS ////////////////////////
///////////////////////////////////////////////////////////////


function niceJacBasis(jac)
    //for our specific jacs, returns the basis Z/(p+1/2)^2 x Z2^2
    wp := [p[1] : p in Roots(HyperellipticPolynomials(Curve(jac)))];

    repeat
        firstpoint := Random(jac);
    until Order(firstpoint) eq ((p+1) div 2);
    firstwp := aboveTwo(firstpoint);

    repeat
        secpoint := Random(jac);
    until Order(secpoint) eq ((p+1) div 2) and aboveTwo(secpoint) ne firstwp;
    secwp := aboveTwo(secpoint);

    lastpointto := firstpoint + secpoint;
    lastwp := aboveTwo(lastpointto);

    P3 := jac!(Divisor(Curve(jac)![wp[firstwp[1]], 0]) + Divisor(Curve(jac)![wp[secwp[1]], 0]));
    P4 := jac!(Divisor(Curve(jac)![wp[firstwp[1]], 0]) + Divisor(Curve(jac)![wp[lastwp[1]], 0]));

    return [firstpoint, secpoint, P3, P4];
end function;



///////////////////////////////////////////////////////////////
///////////////////////// TESITNG... //////////////////////////
///////////////////////////////////////////////////////////////


//here we test out some of these different functionalities
//we get the two rosenhian invariants and construct their (general) kummers
ros1 := MuToRosenhain(K[2]);
ros2 := MinMuToRosenhain(K[2]);

C_ros1 := HyperellipticCurve(X*(X-1)*&*[X - Fp!r : r in ros1]);
J_ros1 := Jacobian(C_ros1);
K_ros1 := KummerSurface(J_ros1);

C_ros2 := HyperellipticCurve(X*(X-1)*&*[X - Fp!r : r in ros2]);
J_ros2 := Jacobian(C_ros2);
K_ros2 := KummerSurface(J_ros2);

//we also construct their squared kummer surfaces
K_fast1 := K;
K_fast2 := MinSupersingularKummerSurfaceFromMontgomeryCurve(alpha);

//lastly, we construct the K^gen for J_alpha
//these objects should also be viewed as the ones in section 2, figure 1
K_alpha := KummerSurface(J_alpha);

Mfast1ros1 := M_kummer(ros1, K_fast1[2]);      //between K_fast and K_ros1
Mfast1ros2 := M_kummer(ros2, K_fast1[2]);

Mfast2ros1 := M_kummer(ros1, K_fast2[2]);      //between K_fast and K_ros1
Mfast2ros2 := M_kummer(ros2, K_fast2[2]);

// if Mfast1ros1 ne Mfast1ros2 then
//     print "ros1 not equal to ros2";
// end if;

//verifies that the constructed matrices map a point 
Z1 := K_ros1!Eltseq(Matrix([RandomKummerPoint(K_fast1)])*Mfast1ros1);
Z2 := K_ros2!Eltseq(Matrix([RandomKummerPoint(K_fast1)])*Mfast1ros2);

//verifies that the composition of constructed matrices map a point correctly
wicked := K_ros2!Eltseq(Matrix([Eltseq(Matrix([Eltseq(MumMapDown(Random(J_ros1)))])*Mfast1ros1^-1)])*Mfast1ros2);

//verifies that the formulas were derived correctly
assert MyDefPol(C_ros1) eq poly!DefiningPolynomial(K_ros1);
assert MyDefPol(C_alpha) eq poly!DefiningPolynomial(K_alpha);

//the choice in the construction is equal either to ros1 or ros2 so set it to equal this
if C_rosenhain eq C_ros1 then
    C_kap := C_ros1;
    J_kap := J_ros1;
    K_kap := K_ros1;
elif C_rosenhain eq C_ros2 then
    C_kap := C_ros2;
    J_kap := J_ros2;
    K_kap := K_ros2;
else assert 3 eq 5;
end if;

//to verify that random points get mapped through kappa
repeat
    P1 := Random(C_alpha);
    P2 := Random(C_alpha);
    D := J_alpha!(Divisor(P1) + Divisor(P2));
until Degree(D[2]) ne 3;
D1 := K_alpha!D;
D2 := K_kap!(BaseChange(K_kap, Fp2)!BaseChange(J_kap, Fp2)!JKappa(D, kappa));

k := Eltseq(D1);
kprimeres := Eltseq(D2);

testifmapworks := evalKappastarstar2(D1, kappa, K_kap);
test := evalKappastarstar(D1, kappa);
twotors_alpha := GetAllTwoTorsion(K_alpha);
twotors_ros1 := GetAllTwoTorsion(K_ros1);

//tests adding two torsion on general kummer surfaces
//by comparing against the result from the Jacobian
j := (p+1) div 2;
repeat
    P := Random(J_alpha); 
    P := (j div 2) *P; 
until not IsZero(P);
assert IsZero(2*P);

Q := Random(J_alpha);

K1 := K_alpha!P; K2 := K_alpha!Q;
assert AddTwo(K1, K2) eq K_alpha!(P+Q);

