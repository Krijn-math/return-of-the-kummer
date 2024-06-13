// Contains more maps described in Section 2 of the accompanying paper. 
// This extends the maps described by Costello in Maps.m

//very ugly hack to ensure we dont overload files
if assigned is_main_script then
    filename := "file_loader.m";
    Write(filename, "\n" : Overwrite := true);
else
    is_main_script := true;
    print "moremaps.m is being executed directly.";
    filename := "file_loader.m";

    files := [
        "../costello-code/Params.m",
        "../costello-code/Kummer.m",
        "../costello-code/Maps.m",
        "../section2/invariants.m"
        ];
    Write(filename, "\n" : Overwrite := true);
    for file in files do
        tmp :=  "load '" cat file cat "'; \n"; 
        Write(filename, tmp);
    end for;
end if;
load "file_loader.m";

///////////////////////////////////////////////////////////////
////////////// MAPS FOR CURVES AND ROSENHAINS /////////////////
///////////////////////////////////////////////////////////////

function Invar(b0, b1, g0, g1)
    // Given beta = b0 + i*b1 and gamma = g0 + i*g1
    // that define the curve C_alpha (see 2018/850),
    // compute the Rosenhain invariants of that curve
 	lambda := -(b0*g1+b1*g0)*(b0*g0+b1*g1)/((b0*g0-b1*g1)*(b0*g1-b1*g0));
    mu := (b0*g0 + b1*g1)*(b0*g0 - b1*g1)/((b0*g1 + b1*g0)*(b0*g1 - b1*g0));
    nu := - (b0*g0 + b1*g1)^2/(b0*g1 - b1*g0)^2;
    return lambda, mu, nu;
end function;

function CurveToRos(C, beta, gamma)

    // Given a curve C_alpha defined by 
    // beta and gamma (see Section 3 of 2018/850),
    // compute the corresponding Rosenhain invariants

	b0:=ElementToSequence(beta)[1];
	b1:=ElementToSequence(beta)[2];
	g0:=ElementToSequence(gamma)[1];
	g1:=ElementToSequence(gamma)[2];

	z1:=b0/b1;
	z2:=g0/g1;
	z3:=-g0/g1;
	z4:=-b1/b0;
	z5:=-g1/g0;
	z6:=g1/g0;

    //see page 15
 	lambda, mu, nu := Invar(b0, b1, g0, g1);

    assert nu eq lambda*mu;

    //all of this is just to check
    C_rosenhain := HyperellipticCurve(X*(X-1)*(X-lambda)*(X-mu)*(X-nu));
    assert IsIsomorphic(C, C_rosenhain);

    a := z2 - z4;
    b := -a*z1;
    c := z2 - z1;
    d := -c*z4;
    e2 := a*c*(a-c)*(a-nu*c)*(a-mu*c)*(a-lambda*c);

    if IsSquare(e2) then e := Sqrt(e2);
    else
        //clean up sometime
        twb0 := -b1; twb1 := b0;
        twg0 := -g1; twg1 := g0;

        b0 := twb0; b1 := twb1;
        g0 := twg0; g1 := twg1;

 	    lambda, mu, nu := Invar(b0, b1, g0, g1);
        assert nu eq lambda*mu;

        C_rosenhain := HyperellipticCurve(X*(X-1)*(X-lambda)*(X-mu)*(X-nu));
        assert IsIsomorphic(C, C_rosenhain);
        z1:=b0/b1;
        z2:=g0/g1;
        z3:=-g0/g1;
        z4:=-b1/b0;
        z5:=-g1/g0;
        z6:=g1/g0;

        a := z2 - z4;
        b := -a*z1;
        c := z2 - z1;
        d := -c*z4;
        e2 := a*c*(a-c)*(a-nu*c)*(a-mu*c)*(a-lambda*c);

        assert IsSquare(e2);
        e := Sqrt(e2);

        // //this was the old way
        // if verbose then print "\nWARNING!!! ENTERING DANGER ZONE!!!\nLine 32 MoreMaps.m\n"; end if;
        // e := Sqrt(Fp2!e2); //KR: this is me doing improv.
    end if;

    return [lambda, mu, nu];
end function;

//trying to keep track if we twist when we apply this function
twisting := false;

function MapToRosenhain(C, beta, gamma)
    //this will be the kappa map on the curves, later induce on jac

	b0:=ElementToSequence(beta)[1];
	b1:=ElementToSequence(beta)[2];
	g0:=ElementToSequence(gamma)[1];
	g1:=ElementToSequence(gamma)[2];

	z1:=b0/b1;
	z2:=g0/g1;
	z3:=-g0/g1;
	z4:=-b1/b0;
	z5:=-g1/g0;
	z6:=g1/g0;

    //see page 15
 	lambda, mu, nu := Invar(b0, b1, g0, g1);

    assert nu eq lambda*mu;

    C_rosenhain := HyperellipticCurve(X*(X-1)*(X-lambda)*(X-mu)*(X-nu));
    assert IsIsomorphic(C, C_rosenhain);

    a := z2 - z4;
    b := -a*z1;
    c := z2 - z1;
    d := -c*z4;
    e2 := a*c*(a-c)*(a-nu*c)*(a-mu*c)*(a-lambda*c);

    if IsSquare(e2) then e := Sqrt(e2);
    else
        //what if we twist?     clean this up into neat function
        twisting := true;
        twb0 := -b1; twb1 := b0;
        twg0 := -g1; twg1 := g0;

        b0 := twb0; b1 := twb1;
        g0 := twg0; g1 := twg1;

 	    lambda, mu, nu := Invar(b0, b1, g0, g1);
        assert nu eq lambda*mu;

        C_rosenhain := HyperellipticCurve(X*(X-1)*(X-lambda)*(X-mu)*(X-nu));
        assert IsIsomorphic(C, C_rosenhain);
        z1:=b0/b1;
        z2:=g0/g1;
        z3:=-g0/g1;
        z4:=-b1/b0;
        z5:=-g1/g0;
        z6:=g1/g0;

        a := z2 - z4;
        b := -a*z1;
        c := z2 - z1;
        d := -c*z4;
        e2 := a*c*(a-c)*(a-nu*c)*(a-mu*c)*(a-lambda*c);

        assert IsSquare(e2);
        e := Sqrt(e2);
    end if;

    return [* [a, b, c, d, e], C, C_rosenhain *];
end function;

function MapToRosenhain2(C, beta, gamma)
    //this will be the kappa map on the curves, later induce on jac

	b0:=ElementToSequence(beta)[1];
	b1:=ElementToSequence(beta)[2];
	g0:=ElementToSequence(gamma)[1];
	g1:=ElementToSequence(gamma)[2];

	z1:=b0/b1;
	z2:=g0/g1;
	z3:=-g0/g1;
	z4:=-b1/b0;
	z5:=-g1/g0;
	z6:=g1/g0;

    //see page 15
 	lambda := -(b0*g1+b1*g0)*(b0*g0+b1*g1)/((b0*g0-b1*g1)*(b0*g1-b1*g0));
    mu := (b0*g0 + b1*g1)*(b0*g0 - b1*g1)/((b0*g1 + b1*g0)*(b0*g1 - b1*g0));
    nu := - (b0*g0 + b1*g1)^2/(b0*g1 - b1*g0)^2;

    assert nu eq lambda*mu;

    C_rosenhain := HyperellipticCurve(X*(X-1)*(X-lambda)*(X-mu)*(X-nu));
    assert IsIsomorphic(C, C_rosenhain);

    a := z2 - z4;
    b := -a*z1;
    c := z2 - z1;
    d := -c*z4;
    e2 := a*c*(a-c)*(a-nu*c)*(a-mu*c)*(a-lambda*c);

    if IsSquare(e2) then e := Sqrt(e2);
    else
        mu := 1/mu;
        nu := lambda*mu;
        C_rosenhain := HyperellipticCurve(X*(X-1)*(X-lambda)*(X-mu)*(X-nu));
        assert IsIsomorphic(C, C_rosenhain);
        e2 := a*c*(a-c)*(a-nu*c)*(a-mu*c)*(a-lambda*c);
        assert IsSquare(e2);
        e := Sqrt(e2);
    end if;

    return [* [a, b, c, d, e], C, C_rosenhain *], [lambda, mu, nu];
end function;

///////////////////////////////////////////////////////////////
////////////////////////// KAPPA MAPS /////////////////////////
///////////////////////////////////////////////////////////////


//required for the file to work
//showing that kappa works if e is over Fp
kappa := MapToRosenhain(C_alpha, beta, gamma);
C_rosenhain := kappa[3];
J_rosenhain := Jacobian(C_rosenhain);
ros := CurveToRos(C_alpha, beta, gamma);

function Kappa(P, kappa)
    //given a point P on curve C and a map kappa given as
    //      1. the values a, b, c, d, e to define the Mobius transform
    //      2. the domain curve C
    //      3. the isomorphic codomain curve C',
    // outputs the image point P
    a, b, c, d, e := Explode(kappa[1]);
    domain := kappa[2];
    codomain := kappa[3];

    assert domain eq Curve(P);

    x := P[1];
    y := P[2];
    if c*P[1] + d ne 0 then
        kappax := (a*P[1] + b)/(c*P[1] + d);
        kappay := e*P[2]/(c*P[1] + d)^3;
        return codomain![kappax, kappay];       
    end if;

    return codomain![1, 0, 0];
end function;


function JKappa(D, kappa)
    // given a map kappa as in the function 
    // 'Kappa()' above, this performs it on the Jacobian
    a, b, c, d, e := Explode(kappa[1]);
    domain := kappa[2];
    codomain := kappa[3];

    if Degree(D[2]) eq 3 then
        //this is an unusual error, based on Magma's way to represent elements in Mumford coordinates
        //an edge case, never happens in cryptographic applications, and can manually be avoided
        print "todo with infinity";
        assert false;
    end if;

    u0, u1, u2 := Explode(Coefficients(D[1] + x^5));
    v0, v1 := Explode(Coefficients(D[2] + x^5));


    //see page 5 eq (6) of Costello (2018/850)
    l1 := c^2*u0 - c*d*u1 + d^2;
    l2 := a*d - b*c;
    if l1*l2 eq 0 then
        //this means kappa maps one of the points to inf
        x1 := Roots(D[1])[1][1];
        x2 := Roots(D[1])[2][1];
        y1 := Evaluate(D[2], x1);
        y2 := Evaluate(D[2], x2);
        P1 := domain![x1, y1];
        P2 := domain![x2, y2];
        T, phi := IsIsomorphic(domain, codomain); assert T;
        return Jacobian(codomain)!( Divisor(phi(P1)) + Divisor(phi(P2)) );
    end if;

    l1inv := l1^-1;
    el1l2 := e*((l1^2*l2)^-1);

    u1p := l1inv*(
        (a*d + b*c)*u1
        - 2*a*c*u0
        - 2*b*d
        );

    u0p := l1inv*(
        a^2*u0
        - a*b*u1
        + b^2
        );

    v1p := el1l2*(
        c^2*(c*u1 - 3*d)*(u0*v1 - u1*v0)
        + c*v0*(c^2*u0 - 3*d^2)
        + d^3*v1
        );

    v0p := -el1l2*(
        a*c^2*(u0*u1*v1 - u1^2*v0 + u0*v0)
        - c*(2*a*d + b*c)*(u0*v1 - u1*v0)
        - d*(a*d + 2*b*c)*v0
        + b*d^2*v1
        );

    return Jacobian(codomain)![x^2 + u1p*x + u0p, v1p*x + v0p];
end function;

///////////////////////////////////////////////////////////////
//////////// GENERAL AND SQUARED KUMMER SURFACES //////////////
///////////////////////////////////////////////////////////////


function M_kummer(ros, thetas)
    //the map M given by Chung Costello Smith (2016/777)
    //to map between the general and squared kummer surface
    //for a kummer coming from rosenhain invariants

    lambda, mu, nu := Explode(ros);

    a, b, c, d := Explode(thetas);

    //this matrix becomes more obvious when viewed in the Weierstrass values, e.g. 
    // w3 = 1, w4 = lambda, w5 = mu and w6 = nu
    M := Matrix([
        [    (nu-lambda)/a,  (mu*nu - lambda)/a,  lambda*nu*(mu - 1)/a,    lambda*nu*(mu*nu - lambda)/a],
        [      (mu - 1)/b,  (mu*nu - lambda)/b,    mu*(nu - lambda)/b,          mu*(mu*nu - lambda)/b],
        [ (lambda - mu)/c,  (lambda - mu*nu)/c,  lambda*mu*(1 - nu)/c,   lambda*mu*(lambda - mu*nu)/c],
        [       (1 - nu)/d,  (lambda - mu*nu)/d,    nu*(lambda - mu)/d,           nu*(lambda - mu*nu)/d]
    ]);
    return M;
end function;


///////////////////////////////////////////////////////////////
////////// MAPS WITH SQUARED KUMMERS AND ROSENHAINS ///////////
///////////////////////////////////////////////////////////////


function BadRosenhainToKummer(D, ros, K)
    //returns the kummer point according to 2016/777 Definition 1
    //for those elements P in Jac whose images would have a zero coord

    //as this almost never happens, we avoid these edge cases manually

    print "IMPLEMENTED ROSENHAIN TO KUMMER FAILED";

    return [Fp!0,Fp!0,Fp!0,Fp!0];
end function;

function RosenhainToKummer(D, ros, K)
    //based on MuKummer (2016/366)
    //the more general map, does not assume Scholten's construction

    if D eq Parent(D)!0 then return K[2]; end if;

    if Degree(D[2]) eq 3 then
        //this is an unusual error, based on Magma's way to represent elements in Mumford coordinates
        //an edge case, never happens in cryptographic applications, and can manually be avoided
        print "todo with infinity";
        assert false;
    end if;

    u0, u1, u2 := Explode(Coefficients(D[1] + x^6));

    if Degree(D[1]) lt 2 then
        u := -u0;
        //Alg 1 from 2016/777
        a, b, c, d := Explode(K[2]);
        t1 := u - 1; t2 := u - ros[1]; t3 := u - ros[2]; t4 := u - ros[3];
        return [Fp!(a*t1*t3), Fp!(b*t2*t4), Fp!(c*t1*t4), Fp!(d*t2*t3)];
    end if;

    if u0 eq 0 then
        //use definition 1 from 2016/777 and special approach
        wp := [0,0,1] cat ros;
        L12 := Parent(D)![x, 0];
        L34 := Parent(D)![(x- wp[3])*(x - wp[4]), 0];
        L56 := Parent(D)![(x- wp[5])*(x - wp[6]), 0];

        tmp := D + L12;
        u0, u1, u2 := Explode(Coefficients(tmp[1] + x^6));

        if u0 ne 0 then
            Q := RosenhainToKummer(tmp, ros, K);
            return [Q[2], Q[1], Q[4], Q[3]]; 
        end if;

        tmp := D + L34;
        u0, u1, u2 := Explode(Coefficients(tmp[1] + x^6));

        if u0 ne 0 then
            Q := RosenhainToKummer(tmp, ros, K);
            return [Q[4], Q[3], Q[2], Q[1]]; 
        end if;

        tmp := D + L56;
        u0, u1, u2 := Explode(Coefficients(tmp[1] + x^6));

        if u0 ne 0 then
            Q := RosenhainToKummer(tmp, ros, K);
            return [Q[3], Q[4], Q[1], Q[2]]; 
        end if;

        return BadRosenhainToKummer(D, ros, K);
    end if;


    //we only need v0, the x^5 is a trick to make 0 work
    v0 := Coefficients(D[2] + x^5)[1];

    lambda, mu, nu := Explode(ros);
    //params are okay now, we apply Alg 3 of muKummer

    T1 := mu - u0;
    T2 := lambda*nu - u0;
    T3 := nu - u0;
    T4 := lambda*mu - u0;
    T5 := lambda + u1;
    T7 := u0*((T5 + mu)*T3);
    T5 := u0*((T5 + nu)*T1);
    T6 := u0*((mu + u1)*T2 + T2);
    T8 := u0*((nu + u1)*T4 + T4);
    T1 := v0^2;
    T5 := T5 - T1;
    T6 := T6 - T1;
    T7 := T7 - T1;
    T8 := T8 - T1;

    P := C(K[2], [T5, T6, T7, T8]);
    if P eq [0,0,0,0] then
        <D, ros, K>;
        <T1, T2, T3, T4, T5, T6, T7, T8>;
        assert 3 eq 5;
    end if;

    assert OnKummer(P, K);
    return [Fp!p : p in P];
end function;


function Fp2RosenhainToKummer(D, ros, K)
    //based on MuKummer (2016/366)
    //the more general map, does not assume Scholten's construction e.g. nu = lambda*mu

    if D eq Parent(D)!0 then return K[2]; end if;

    if Degree(D[2]) eq 3 then
        //this is an unusual error, based on Magma's way to represent elements in Mumford coordinates
        //an edge case, never happens in cryptographic applications, and can manually be avoided
        print "todo with infinity";
        assert false;
    end if;

    u0, u1, u2 := Explode(Coefficients(D[1] + x^6));

    if Degree(D[1]) lt 2 then
        u := -u0;
        //Alg 1 from 2016/777
        a, b, c, d := Explode(K[2]);
        t1 := u - 1; t2 := u - ros[1]; t3 := u - ros[2]; t4 := u - ros[3];
        return [Fp2!(a*t1*t3), Fp2!(b*t2*t4), Fp2!(c*t1*t4), Fp2!(d*t2*t3)];
    end if;

    if u0 eq 0 then
        //use definition 1 from 2016/777 and special approach
        wp := [0,0,1] cat ros;
        L12 := Parent(D)![x, 0];
        L34 := Parent(D)![(x- wp[3])*(x - wp[4]), 0];
        L56 := Parent(D)![(x- wp[5])*(x - wp[6]), 0];

        tmp := D + L12;
        u0, u1, u2 := Explode(Coefficients(tmp[1] + x^6));

        if u0 ne 0 then
            Q := Fp2RosenhainToKummer(tmp, ros, K);
            return [Q[2], Q[1], Q[4], Q[3]]; 
        end if;

        tmp := D + L34;
        u0, u1, u2 := Explode(Coefficients(tmp[1] + x^6));

        if u0 ne 0 then
            Q := Fp2RosenhainToKummer(tmp, ros, K);
            return [Q[4], Q[3], Q[2], Q[1]]; 
        end if;

        tmp := D + L56;
        u0, u1, u2 := Explode(Coefficients(tmp[1] + x^6));

        if u0 ne 0 then
            Q := Fp2RosenhainToKummer(tmp, ros, K);
            return [Q[3], Q[4], Q[1], Q[2]]; 
        end if;

        return BadRosenhainToKummer(D, ros, K);
    end if;

    //we only need v0, the x^5 is a trick to make 0 work
    v0 := Coefficients(D[2] + x^5)[1];
   

    lambda, mu, nu := Explode(ros);
    //params are okay now, we apply Alg 3 of muKummer

    T1 := mu - u0;
    T2 := lambda*nu - u0;
    T3 := nu - u0;
    T4 := lambda*mu - u0;
    T5 := lambda + u1;
    T7 := u0*((T5 + mu)*T3);
    T5 := u0*((T5 + nu)*T1);
    T6 := u0*((mu + u1)*T2 + T2);
    T8 := u0*((nu + u1)*T4 + T4);
    
    T1 := v0^2;    
    T5 := T5 - T1;
    T6 := T6 - T1;
    T7 := T7 - T1;
    T8 := T8 - T1;

    P := C(K[2], [T5, T6, T7, T8]);
    if P eq [0,0,0,0] then
        <D, ros, K>;
        <T1, T2, T3, T4, T5, T6, T7, T8>;
        assert 3 eq 5;
    end if;

    assert OnKummer(P, K);
    return [Fp2!p : p in P];
end function;

function RosenhainToKummer2(D, ros, K)
    //based on CCS (2016/777) Algorithm 1 which should be equivalent to the algorithm from muKummer
    //the more general map, does not assume Scholten's construction
    a, b, c, d := Explode(K[2]);
    l, m, n := Explode(ros);

    if IsZero(D) then return K[2]; end if;

    if Degree(D[1]) eq 1 then
        u0, u1 := Explode(Coefficients(D[1]));
        v0 := Coefficients(D[2] + x^3)[1];
        T1 := u0 - 1;
        T2 := u0 - l;
        T3 := u0 - m;
        T4 := u0 - n;
        P := [a*T1*T3, b*T2*T4, c*T1*T4, d*T2*T3];
        assert OnKummer(P, K);
        return P;
    end if;

    u0, u1, u2 := Explode(Coefficients(D[1]));
    //we only need v0, the x^3 is a trick to make 0 work
    v0 := Coefficients(D[2] + x^3)[1];

    T1 := u1 + l;
    T2 := u1 + 1;
    T3 := v0^2;
    T4 := u0*(u0 - 1*m)*(T1 + n);
    T5 := u0*(u0 - l*n)*(T2 + n);
    T6 := u0*(u0 - 1*n)*(T1 + m);
    T7 := u0*(u0 - l*m)*(T2 + n);

    P := [a*T4 + T3, b*T5 + T3, c*T6 + T3, d*T7 + T3];

    if P eq [0,0,0,0] then
        <D, ros, K>;
        <T1, T2, T3, T4, T5, T6, T7>;
        assert 3 eq 5;
    end if;
    assert OnKummer(P, K);
    return P;
end function;

function FastToMapBetweenGeneral(mus)
    //given the theta coordinates of a squared kummer surfaces
    //returns the map between the two different sets of rosenhains one can derive
    //e.g. lambda, mu, nu and lambda, 1/mu, 1/nu, by different choice of square root

    ros1 := MuToRosenhain(mus);
    ros2 := MinMuToRosenhain(mus);

    poly<X> := PolynomialRing(Fp);
    C_ros1 := HyperellipticCurve(X*(X-1)*&*[X - Fp!r : r in ros1]);
    J_ros1 := Jacobian(C_ros1);
    K_ros1 := KummerSurface(J_ros1);

    C_ros2 := HyperellipticCurve(X*(X-1)*&*[X - Fp!r : r in ros2]);
    J_ros2 := Jacobian(C_ros2);
    K_ros2 := KummerSurface(J_ros2);

    //uses the formulas from Cheng, Costello, Smith (2016/777)
    //to derive the two matrices K^sqr -- > K^gen --> K^sqr
    M1 := M_kummer(ros1, mus);
    M2 := M_kummer(ros2, mus);

    res := M1^-1*M2;

    return [* res, K_ros1, K_ros2 *];
end function;



///////////////////////////////////////////////////////////////
////////////// MAPS FOR ELLIPTIC CURVE E_alpha ////////////////
///////////////////////////////////////////////////////////////


function FullToJac(P)
    //the full map from P on E_alpha to the Jacobian J_ros
        D_alpha := eta(P);              //mapped to J_alpha
        D_rosenhain := J_rosenhain!JKappa(D_alpha, kappa);      //mapped to the Rosenhain
        KD := RosenhainToKummer(D_rosenhain, ros, K);   //mapped down to the Kummer
        assert OnKummer(KD, K);
        return D_rosenhain;
end function;

function FullToKummer(P)
    //the full map from P on E_alpha to the squared Kummer surface

    /* this is the nice case, where e is in fp, and everything works as it should*/
    if kappa[1][5] in Fp then
        D_alpha := eta(P);              //mapped to J_alpha
        D_rosenhain := J_rosenhain!JKappa(D_alpha, kappa);      //mapped to the Rosenhain
        KD := RosenhainToKummer(D_rosenhain, ros, K);   //mapped down to the Kummer
        assert OnKummer(KD, K);
        return KD;
    else
    /*
    Here we map points in J_alpha to imaginairy points in
    J_rosenhain(Fp2), but only the b(x) polynomial is imaginairy. Mapping them down to the Kummer still works
    we avoid this case using the lemma on twists of Kummers, so this doesnt happen anymore
    */
        print "SHOULD NOT HAPPEN ANYMORE";

        D_alpha := eta(P);
        Di := BaseChange(J_rosenhain, Fp2)!JKappa(D_alpha, kappa);
        KD := RosenhainToKummer(Di, ros, K);   //mapped down to the Kummer
        assert OnKummer(KD, K);
        return KD;
    end if;
end function;

function GetPair()
    //generates a random P on E_alpha, then maps down P down to the Kummer surface
    //returns both P and its associated KD
    P := Random(E_alpha);
    D_alpha := eta(P);
    D_rosenhain := J_rosenhain!JKappa(D_alpha, kappa);
    KD := RosenhainToKummer(D_rosenhain, ros, K);
    return P, KD;
end function;

function AlphaAndPointToKummerUnderTheHood(alpha, P)
    //given an alpha value and a point P on E_alpha, maps them down to the Kummer surface
    //using the explicit maps
    C_alpha, J_alpha, beta, gamma, zs := SupersingularAbelianSurfaceFromMontgomeryCurve(alpha);
    E_alpha := EllipticCurve(x*(x- alpha)*(x - 1/alpha));
    K := SupersingularKummerSurfaceFromMontgomeryCurve(alpha);

    r1:=(alpha-1/alpha)^(p-1); r2:=alpha^(p-1); r3:=1/alpha^(p-1);
    betahat:=Sqrt(r3-r2);
    w:=Sqrt((r2-1)^2*(1-r1)*r3);

    //curves/Jacobian defined over Fp2
    Etil_alpha:=EllipticCurve((x-Fp2!r1)*(x-Fp2!r2)*(x-Fp2!r3));
    Ctil_alpha:=HyperellipticCurve((x^2-r1)*(x^2-r2)*(x^2-r3));
    Jtil_alpha:=Jacobian(Ctil_alpha);

    kappa := MapToRosenhain(C_alpha, beta, gamma);
    C_rosenhain := kappa[3];
    J_rosenhain := Jacobian(C_rosenhain);
    J2_rosenhain := BaseChange(J_rosenhain, Fp2);

    //replacing psi to work generally
	assert P in E_alpha;
	xx:=P[1]; yy:=P[2];
	P := Etil_alpha![(betahat/beta)^2*xx+r1,(betahat/beta)^3*yy];

    //replacing rho to work generally
    //map from Etil_alpha(Fp2) to J_alpha(Fp2)
	assert P in Etil_alpha;
	xtil:=P[1]; ytil:=P[2];
	u1:=2*i*(xtil+1)/(xtil-1);
	u0:=-1;
	v1:=-4*i*ytil*(xtil+3)/(w*(xtil-1)^2);
	v0:=4*ytil/(w*(xtil-1));
	P := BaseChange(J_alpha,Fp2)![x^2+u1*x+u0,v1*x+v0];

    //replacing Trace to work generally
    //map from J_alpha(Fp2) down to J_alpha(Fp)
	assert P in BaseChange(J_alpha,Fp2);
	sigP:=Frobenius(P,Fp);
	P := J_alpha!(P+sigP);

    //hence, now we have applied psi, rho, and Tr to P, so P := eta(P)
    //composition map from E_alpha(Fp2) to J_alpha
    EtaP := P;
    DivP := P;

    if kappa[1][5] in Fp then
        D_rosenhain := J_rosenhain!JKappa(DivP, kappa);      //mapped to the Rosenhain
        KD := RosenhainToKummer(D_rosenhain, ros, K);         //mapped down to the Kummer
        assert OnKummer(KD, K);
        return K, KD, C_alpha, J_alpha, J_rosenhain, kappa, EtaP;
    else
    /*
    Here we map points in J_alpha to imaginairy points in
    J_rosenhain(Fp2), but only the b(x) polynomial is imaginairy. Mapping them down to the Kummer still works
    we avoid this case using the lemma on twists of Kummers, so this doesnt happen anymore
    */
        print "SHOULD NOT HAPPEN";
        Di := BaseChange(J_rosenhain, Fp2)!JKappa(DivP, kappa);
        KD := RosenhainToKummer(Di, ros, K);
        assert OnKummer(KD, K);
        return K, KD, C_alpha, J_alpha, J_rosenhain, kappa, EtaP;
    end if;
end function;

function AlphaAndPointToKummer(alpha, P)
    //given alpha and P, returns the kummer surface K and kummer point KD associated to alpha and P
    K, KD := AlphaAndPointToKummerUnderTheHood(alpha, P);
    return K, KD;
end function;

///////////////////////////////////////////////////////////////
///////////// JACOBIAN TO SQUARED KUMMMER /////////////////////
///////////////////////////////////////////////////////////////

function JToKummer(JP)
    // same map as before, but just starting from J
    D_alpha := JP;

    /* this is the nice case, where e is in fp, and everything works as it should*/
    if kappa[1][5] in Fp then
        D_rosenhain := J_rosenhain!JKappa(D_alpha, kappa);      //mapped to the Rosenhain
        KD := RosenhainToKummer(D_rosenhain, ros, K);         //mapped down to the Kummer
        assert OnKummer(KD, K);
        return KD;
    else
    /*
    Here we map points in J_alpha to imaginairy points in
    J_rosenhain(Fp2), but only the b(x) polynomial is imaginairy. Mapping them down to the Kummer still works
    we avoid this case using the lemma on twists of Kummers, so this doesnt happen anymore
    */
        print "SHOULD NOT HAPPEN ANYMORE";

        Di := BaseChange(J_rosenhain, Fp2)!JKappa(D_alpha, kappa);
        KD := RosenhainToKummer(Di, ros, K);
        assert OnKummer(KD, K);
        return KD;
    end if;
end function;

function KernelPointToMont(ker)
    //recomputes the Montgomery coefficient A from a kernel point (x,y)
    //returns the curve E_A

    poly<AX> := PolynomialRing(Fp2);
    lhs := ker[2]^2; 
    rhs := ker[1]^3 + AX*ker[1]^2 + ker[1];
    AA := Roots(lhs - rhs)[1][1];
    E_AA := EllipticCurve([0, AA, 0, 1, 0]);
    test := E_AA!ker;
    return E_AA;
end function;


///////////////////////////////////////////////////////////////
//////////////////// HELPER FUNCTIONS /////////////////////////
///////////////////////////////////////////////////////////////


function niceEval(mapmat, element)
    //helper function used to evaluate a kummer point on a linear map P^3 --> P^3
    //where the mapmat is given by 1. the actual matrix, 2. the starting kummer, 3. the codomain kummer
    matrix := mapmat[1];
    Kstart := mapmat[2];
    Kend := mapmat[3];
    return Eltseq(Matrix([  [Fp!e : e in Eltseq(element)] ])*matrix);
end function;

function invMapmat(mapmat)
    //a helper function to return the inverse of a mapmat in the right format
    return [* mapmat[1]^-1, mapmat[3], mapmat[2] *];
end function;

///////////////////////////////////////////////////////////////
//////////////////////// TESTING... ///////////////////////////
///////////////////////////////////////////////////////////////


//we then test our maps, given above

if kappa[1][5] in Fp then
    for i in [1..10] do
        //we could cater to the inf case, but i just disregarded it for now
        repeat P := Random(C_alpha); until not P in PointsAtInfinity(C_alpha);
        kappaP := C_rosenhain!Kappa(P, kappa);
    end for;

    //now mapping to Jacs
    for i in [1..10] do
        D := Random(J_alpha);
        //we manually avoid the bugged case where the Mumford representation in Magma is unusual
        if Degree(D[2]) eq 3 then
            repeat 
            "TODO: fix inifinty mapping JKappa";
            D := Random(J_alpha);
            until Degree(D[2]) ne 3;
        end if;
        kappaD := J_rosenhain!JKappa(D, kappa);
    end for;

    //so a map from E_alpha --> J_rosenhain would be
    for i in [1..10] do
        JP := J_rosenhain!JKappa(eta(Random(E_alpha)), kappa);
    end for;
else
    C2 := BaseChange(C_rosenhain, Fp2);
    J2 := BaseChange(J_rosenhain, Fp2);
end if;

//now lets use muKummer to map down to K
//note: K is precisely the surface associated to the J_rosenhain
//compare construction in Params.m

//note: what we have as mu1, mu2, mu3, mu4 are a, b, c, d in muKummer
//this should not be confused with the a, b, c, d, e, I used in kappa

if kappa[1][5] in Fp then
    for i in [1..10] do
        P := Random(E_alpha);           //random point on E_alpha
        D_alpha := eta(P);              //mapped to J_alpha
        if Degree(D_alpha[2]) eq 3 then
            repeat 
            "todo fix inifinty mapping JKappa";
            P := Random(E_alpha);           //random point on E_alpha
            D_alpha := eta(P); 
            until Degree(D_alpha[2]) ne 3;
        end if;
        D_rosenhain := J_rosenhain!JKappa(D_alpha, kappa);      //mapped to the Rosenhain
        KD := RosenhainToKummer(D_rosenhain, ros, K);         //mapped down to the Kummer
        assert OnKummer(KD, K);
    end for;
else
    /*
    we avoid this case using the lemma on twists of Kummers, so this doesnt happen anymore
    */
    print "SHOULD NOT HAPPEN ANYMORE";

    for i in [1..10] do
        P := Random(E_alpha);           //random point on E_alpha
        D_alpha := eta(P);              //mapped to J_alpha
        //we manually avoid the bugged case where the Mumford representation in Magma is unusual
        if Degree(D_alpha[2]) eq 3 then
            repeat 
            "todo fix inifinty mapping JKappa";
            P := Random(E_alpha);           //random point on E_alpha
            D_alpha := eta(P); 
            until Degree(D_alpha[2]) ne 3;
        end if;
        Di := BaseChange(J_rosenhain, Fp2)!JKappa(D_alpha, kappa);      //mapped to the Rosenhain (imaginairy)
        KD := RosenhainToKummer(Di, ros, K);         //mapped down to the Kummer
        assert OnKummer(KD, K);
    end for;
end if;


// print "mapping down to Kummer works!!!\n";
// print "MoreMaps.m done\n";