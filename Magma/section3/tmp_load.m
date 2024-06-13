// This function is a helper file containing loads of Kummer functions duplicated from somewhere else
// We use this in wij_squared_kummer.m
// This was required in some situations to be able to work with the right Kummer surface properly.

normalise:=function(P)

	/*

	Normalizes Kummer points in P^3, mainly for equality and correctness checking. Sets the 4th coordinate as 1, unless there is a zero coordinate, in which case it's a 2-torsion point, where we set the 1st coordinate as 1.

	INPUT: - P: Point in P^3, represented as a 4-tuple
	OUTPUT: - Normalised point equivalent to P

	*/

	if &*P ne 0 then
		return [P[1]/P[4],P[2]/P[4],P[3]/P[4],P[4]/P[4]];
	else 
		return [P[1]/P[1],P[2]/P[1],P[3]/P[1],P[4]/P[1]];
	end if;

end function;


H:=function(P);

	/*

	The 4-way Hadamard transform

	INPUTS: - A tuple of four projective field elements [x,y,z,t]
	OUTPUTS: - The Hadamard transform [x+y+z+t,x+y-z-t,x-y+z-t,x-y-z+t]		

	*/

	T1:=P[1]+P[2]; T2:=P[3]+P[4]; T3:=P[1]-P[2]; T4:=P[3]-P[4];

	return [T1+T2,T1-T2,T3+T4,T3-T4];

end function;

S:=function(P);

	/*

	The 4-way squaring

	INPUTS: - A tuple of four projective field elements [x,y,z,t]
	OUTPUTS: - The coordinate-wise squarings [x^2,y^2,z^2,t^2]		

	*/

	return [P[1]^2,P[2]^2,P[3]^2,P[4]^2];

end function;

C:=function(V,W)

	/*

	The 4-way coordinate-wise multiplication of 2 tuples

	INPUTS: - Two tuples of four projective field elements
	OUTPUTS: - One 4-tuple of their coordinate-wise products	

	*/

	return [V[1]*W[1],V[2]*W[2],V[3]*W[3],V[4]*W[4]];

end function;

Invert4Constants:=function(P)

	/*

	The 4-way inversion in projective 3-space

	INPUTS: - One tuple of 4-elements in P^3 
	OUTPUTS: - A tuple of elements projectively equivalent to their inverses

	*/

	pi1:=P[3]*P[4];
	pi2:=pi1*P[1];
	pi1:=pi1*P[2];
	pi3:=P[1]*P[2];
	pi4:=pi3*P[3];
	pi3:=pi3*P[4];

	res := [pi1,pi2,pi3,pi4];
	assert &*res ne 0;
	
	return res;

end function;

Invert4Constants:=function(P)

	/*

	The 4-way inversion in projective 3-space

	INPUTS: - One tuple of 4-elements in P^3 
	OUTPUTS: - A tuple of elements projectively equivalent to their inverses

	*/

	pi1:=P[3]*P[4];
	pi2:=pi1*P[1];
	pi1:=pi1*P[2];
	pi3:=P[1]*P[2];
	pi4:=pi3*P[3];
	pi3:=pi3*P[4];

	return [pi1,pi2,pi3,pi4];

end function;

KummerConstantsFromSquaredThetas:=function(P)
	
	/*

	Computes the Kummer surface constants used in the DBL and DBLADD functions

	INPUTS: - the 4 squared theta constants [mu1,mu2,mu3,mu4]
	OUTPUTS: - the first tuple is projectively equivalent to [1/mu1: 1/mu2: 1/mu3: 1/mu4]
			 - the second tuple is projectively equivalent to [1/mu1h: 1/mu2h: 1/mu3h: 1/mu4h], 
			 where the mujh are the j-th component of the Hadamard transform of [mu1,mu2,mu3,mu4]

	*/
	
	return Invert4Constants(P),Invert4Constants(H(P));

end function;

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

SquaredKummerFromSquaredThetas:=function(thetas)
	
	/*

	Computes all of the Kummer surface constants

	INPUTS: - the 4 squared theta constants [mu1,mu2,mu3,mu4]
	OUTPUTS: - K1: [K_F,K_G,K_H], which define a Kummer surface (see Section 5)
			 - K2: [mu1,mu2,mu3,mu4], the unchanged input, but part of the full description of a Kummer
			 - K3, K4: the two 4-tuples of projective constants needed in the DBL and DBLADD routines
	*/
	
	mu1:=thetas[1]; mu2:=thetas[2]; mu3:=thetas[3]; mu4:=thetas[4];

	K_F:=(mu1+mu2+mu3+mu4)*(mu1+mu2-mu3-mu4)*(mu1-mu2+mu3-mu4)*(mu1-mu2-mu3+mu4);
	K_F:=K_F/(mu1*mu4-mu2*mu3)/(mu1*mu3-mu2*mu4)/(mu1*mu2-mu3*mu4);
	K_G:=(mu1^2-mu2^2-mu3^2+mu4^2)/(mu1*mu4-mu2*mu3);
	//assert K_G eq (mu1^2-mu2^2+mu3^2-mu4^2)/(mu1*mu3-mu2*mu4);
	K_H:=(mu1^2+mu2^2-mu3^2-mu4^2)/(mu1*mu2-mu3*mu4);
	K_F:=4*K_F^2*mu1*mu2*mu3*mu4;

	K1:=[K_F,K_G,K_H];
	K2:=thetas;
	K3,K4:=KummerConstantsFromSquaredThetas(thetas);

	return [K1,K2,K3,K4];

end function;

OnKummer:=function(P,K)

	/*

	Checks if a given point is on a given Kummer surface.

	INPUTS: - P: Point in P^3, represented as a 4-tuple
 			- K: Kummer surface
	OUTPUT: - boolean: true if P lies on K, false otherwise

	*/

	return 
		K[1][1]*(P[1]*P[2]*P[3]*P[4])
		eq
		(
		(P[1]^2+P[2]^2+P[3]^2+P[4]^2)
		-K[1][2]*(P[1]+P[2])*(P[3]+P[4])
		-K[1][3]*(P[1]*P[2]+P[3]*P[4])
		)^2;

end function;


DBL:=function(P,K);

	/*

	(Pseudo-)doubling of a Kummer point

	INPUTS: - P: Point in P^3, represented as a 4-tuple, lying on...
 			- K: Kummer surface
	OUTPUT: - [2]P 

	*/

	P:=H(P);
	P:=S(P);
	P:=C(P,K[4]);
	P:=H(P);
	P:=S(P);
	P:=C(P,K[3]);

	if OnKummer(P,K) then
		return normalise(P);
	else
		return "somethings wrong";
	end if;
	
end function;

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

eDBLs:=function(P,K,e);

	/*

	Repeated (Pseudo-)doublings of a Kummer point

	INPUTS: - P: Point in P^3, represented as a 4-tuple, lying on...
 			- K: Kummer surface
 			- e: an integer
	OUTPUT: - [2^e]P 
	
	*/

	for j:=1 to e do
		P:=DBL(P,K);
	end for;

	if OnKummer(P,K) then
		return normalise(P);
	else
		return "somethings wrong";
	end if;
	
end function;

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

DBLADD:=function(P,Q,R,K);

	/*

	(Pseudo-)addition of Kummer points

	INPUTS: - P,Q,R: Points in P^3, all represented as a 4-tuple, where R=(Q+-P) lying on...
 			- K: Kummer surface
	OUTPUT: - (Q-+P)
	
	*/

	P:=H(P); U:=H(Q);
	
	Q:=C(P,K[4]);
	P:=C(P,Q);
	Q:=C(Q,U);

	P:=H(P); Q:=H(Q);
	P:=S(P); Q:=S(Q);

	P:=C(P,K[3]); Q:=C(Q,R);

	if OnKummer(P,K) and OnKummer(Q,K) then
		return P,Q;
	else
		return "somethings wrong";
	end if;
	
end function;

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

KummerScalar:=function(P,K,n);

	/*

	Scalar multiplication of Kummer points

	INPUTS: - P: Point in P^3, represented as a 4-tuple, lying on...
 			- K: Kummer surface
 			- n: a positive integer scalar
	OUTPUT: - [n]P
	
	*/

	bits:=IntegerToSequence(n,2);
	
	Pm:=P; Pp:=DBL(P,K); 

	R:=Invert4Constants(P); 

	for i:=#bits-1 to 1 by -1 do
	
		if bits[i] eq 0 then
			Pm,Pp:=DBLADD(Pm,Pp,R,K);
		else
			Pp,Pm:=DBLADD(Pp,Pm,R,K);
		end if;
	end for;
	
	if OnKummer(Pm,K) then
		return normalise(Pm);
	else
		return "somethings wrong";
	end if;
	
end function;

function RosenhainToKummer(D, ros, K)
    //based on MuKummer
    //the more general map, does not assume Scholten's construction

    if D eq Parent(D)!0 then return K[2]; end if;

    if Degree(D[2]) eq 3 then
        //TODO
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

        assert false;
        return 0;
        //return BadRosenhainToKummer(D, ros, K);
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

    //assert OnKummer(P, K);
    return [Fp!p : p in P];
end function;
