// Copyright (c) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE file in the project root for full license information.

/*

This file performs computations as described in Section 5 of the paper.  

Note that various checks of correctness and point normalisations (that would not be used in an actual implementation) are performed throughout.

*/

if assigned is_main_script then
    filename := "file_loader.m";
    Write(filename, "\n" : Overwrite := true);
else
    is_main_script := true;
    print "Kummer.m is being executed directly.";
    filename := "file_loader.m";

    files := [
        "../costello-code/Params.m"
        ];
    Write(filename, "\n" : Overwrite := true);
    for file in files do
        tmp :=  "load '" cat file cat "'; \n"; 
        Write(filename, tmp);
    end for;
end if;
load "file_loader.m";
//load "../costello-code/Params.m";

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

normalise:=function(P)

	/*

	Normalizes Kummer points in P^3, mainly for equality and correctness checking. Sets the 4th coordinate as 1, unless there is a zero coordinate, in which case it's a 2-torsion point, where we set the 1st coordinate as 1.

	INPUT: - P: Point in P^3, represented as a 4-tuple
	OUTPUT: - Normalised point equivalent to P

	*/

	if &*P ne 0 then
		scal := 1/P[4];
		return [P[1]*scal,P[2]*scal,P[3]*scal,P[4]*scal];
	else 
		if P[4] ne 0 then
			scal := 1/P[4];
			return [P[1]*scal,P[2]*scal,P[3]*scal,P[4]*scal];
		elif P[3] ne 0 then
			scal := 1/P[3];
			return [P[1]*scal,P[2]*scal,P[3]*scal,P[4]*scal];
		elif P[2] ne 0 then
			scal := 1/P[2];
			return [P[1]*scal,P[2]*scal,P[3]*scal,P[4]*scal];
		else
			scal := 1/P[1];
			return [P[1]*scal,P[2]*scal,P[3]*scal,P[4]*scal];
		end if;
	end if;

    assert 3 eq 5;
end function;

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

OnKummer:=function(P,K)

	/*

	Checks if a given point is on a given Kummer surface.

	INPUTS: - P: Point in P^3, represented as a 4-tuple
 			- K: Kummer surface
	OUTPUT: - boolean: true if P lies on K, false otherwise

	*/
	if P eq [0,0,0,0] then return false; end if;

	return 
		K[1][1]*(P[1]*P[2]*P[3]*P[4])
		eq
		(
		(P[1]^2+P[2]^2+P[3]^2+P[4]^2)
		-K[1][2]*(P[1]+P[2])*(P[3]+P[4])
		-K[1][3]*(P[1]*P[2]+P[3]*P[4])
		)^2;

end function;

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

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
	    if &*P ne 0 then			//KR: added this to make things work
			return normalise(P);
		else 
		    return normalise(P);
		end if;
	else
		return "somethings wrong";
	end if;
	
end function;

DBLnonormalise:=function(P,K);

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
		return P;
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

	INPUTS: - P,Q,Invert4Constants(R): Points in P^3, all represented as a 4-tuple, where R=(Q+-P) lying on...
 			- K: Kummer surface
	OUTPUT: - 2P and (Q-+P)
	
	*/
	assert OnKummer(P, K);
	assert OnKummer(Q, K);
	// assert OnKummer(R, K);
	tmp := <P, Q, R>;

	P:=H(P); U:=H(Q);
	
	Q:=C(P,K[4]);
	P:=C(P,Q);
	Q:=C(Q,U);

	P:=H(P); Q:=H(Q);
	P:=S(P); Q:=S(Q);

	P:=C(P,K[3]); Q:=C(Q,R);

	if P eq [0,0,0,0] or Q eq [0,0,0,0] then
		"DBLADD failed\n\n";
		printf "P := %o;\n", tmp[1];
		printf "Q := %o;\n", tmp[2];
		printf "R := %o;\n\n", tmp[3];
		assert false;
	end if;

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
	
	if OnKummer(Pm,K) then		//added the second condition to prevent something that fails often
		return normalise(Pm);
	else
		return "somethings wrong";
	end if;
	
end function;


///////////////////////////////////////////////////////////////
/////////////////  KR: MADE THIS THING HERE   /////////////////
///////////////////////////////////////////////////////////////

function ThreePointLadder(P, Q, PmQ, s, K)
    /*
	Computes 3pt-ladder (from SIKE)
	
	Input: projective points P, Q, PmQ = P-Q
		   scalar s, kummer surface K
	Output: P+[m]Q
    */

	bits := Intseq(s, 2);
	
	P0 := Q;
    P1 := P;
	P2 := PmQ;

	for i in bits do
		if i eq 1 then
            P0, P1 := DBLADD(P0, P1, Invert4Constants(P2), K);
		else
            P0, P2 := DBLADD(P0, P2, Invert4Constants(P1), K);
		end if;
	end for;
	
	if OnKummer(P1,K) then		//added the second condition to prevent something that fails often
		return normalise(P1);
	else
		return "somethings wrong";
	end if;
end function;

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

RandomKummerPoint:=function(K)  

	/*

	Computes a random point on a given Kummer surface

	INPUTS: - K: Kummer surface
	OUTPUT: - a random point P on K
	
	*/

	 repeat
		 x := Random(Fp);
	  	 y := Random(Fp);
	     z := Random(Fp);
	     Poly<T>:=PolynomialRing(Fp);
	     Eq := K[1][1]*(x*y*z*T)-((x^2+y^2+z^2+T^2)-K[1][2]*(x+y)*(z+T)-K[1][3]*(x*y+z*T))^2;
	     test, t := HasRoot(Eq);
     until test;

     return [x,y,z,t];

end function;

SpecificKummerPoint:=function(K, P)  
	/*
	Assumes one of a, b, c, d is zero.
	Computes a Kummer point on a given Kummer surface,
	with the zero replaced by an Fp-value, if this exists.

	INPUTS: - K: Kummer surface and three coordinates
	OUTPUT: - a point P on K with fourth coordinate
	
	*/

	//P := [a, b, c, d];
	assert &+[1 : p in P | p eq 0] eq 1;

	i := Index(P, 0);
    poly<T>:=PolynomialRing(Fp);
	P := [poly!p : p in P];
	P[i] := T;
	x, y, z, t := Explode(P);
    Eq := K[1][1]*(x*y*z*t)-((x^2+y^2+z^2+t^2)-K[1][2]*(x+y)*(z+t)-K[1][3]*(x*y+z*t))^2;
    test, r := HasRoot(Eq);
	if test then
		P[i] := r;
	    return test, [Fp!p : p in P];
	end if;

	return test, [0,0,0,0];
end function;

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

RandomFullOrderPoint:=function(K);

	/*

	Computes a point on a given Kummer surface whose order is maximal. Used to illustrate various SIDH-like computations. Note that it's not completely random as we force it to lie above special kernels. See the paper.

	INPUTS: - K: Kummer surface
	OUTPUT: - a point P on K
	
	*/

	tau:=(K[1][2]+Random([-1,1])*Sqrt(K[1][2]^2-4))/2; //non-zero coordinate of various 2-torsion points on K
	repeat
		P:=RandomKummerPoint(K);
		Q:=KummerScalar(P,K,((p+1) div 4)); //maximum order
	//until &*Q eq 0;	
	until normalise(Q) in {[tau,0,1,0], [1,0,tau,0], [0,1,0,tau], [0,tau,0,1]};   //KR: replaced this because couldnt fix it otherwise
	
	return P;

end function;

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

IsogenousSquaredThetasFromTorsionKernel:=function(P2,P4)

	/*

	Given a special point of order 2 and a point of order 4 lying above it, this function computes the squared theta constants of the image Kummer surface corresponding to the kernel specified by the torsion points (see the paper), as well as constants used to compute the image of any point under the associated isogeny.

	INPUTS: - P2: a Kummer point of order 2 in one of the two (2,2)-subgroups of interest
			- P4: a Kummer point of order 4 such that P2=[2]P4 on K
	OUTPUT: - mus: a 4-tuple of the squared theta coordinates of the image Kummer
			- pis: some constants used in the isogeny evaluation (next) function, i.e., in the special scaling C. See the paper.
	*/

	HP2:=H(P2); HP4:=H(P4); //save on H(P2)

	// assert P2[3] ne 0;

	// pi1:=HP2[2]*HP4[3];
	// pi2:=HP4[3]*HP2[1];
	// pi3:=HP2[2]*HP4[1]; 
	// pi4:=pi3;

	/*
	This has been commented out because our kernels are always of the form [1,0,tau,0], rather than [1,0,0,tau]. Other setups and instantiations may find the kernel elements to be of the form [1,0,0,tau], and instead want the "else" part of the code below. See the paper for more details. 
	*/

	
	if P2[3] ne 0 then
		pi1:=HP2[2]*HP4[3];
		pi2:=HP4[3]*HP2[1];
		pi3:=HP2[2]*HP4[1]; 
		pi4:=pi3;
	else
		pi1:=HP2[2]*HP4[4];
		pi2:=HP4[4]*HP2[1];
		pi3:=HP2[2]*HP4[1]; 
		pi4:=pi3;
	end if;
	

	pis:=[pi1,pi2,pi3,pi4];
	mus:=C(HP2,pis);
	mus:=H(mus);
	mus:=S(mus);

	return mus,pis;

end function;

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

IsogenyKummerPoint:=function(Q,pis)

	/*

	Evaluating the (2,2) isogeny from the above function on a general point on the domain Kummer. 

	INPUTS: - Q: any non-kernel point on a given Kummer K
	OUTPUT: - varphi(Q): the image of varphi on Qs

	*/

	Q:=H(Q);
	Q:=C(Q,pis);
	Q:=H(Q);
	Q:=S(Q);

	return Q;

end function;

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

/*
we do some "twisting" that we should look more closely at, but seems to solve 
our issues of well-defined squares
*/

TwistKummer := function(K)
	twister := [-1, -1, 1, 1];
	mus := K[2];
	twistmus := normalise(C(twister, mus));
	return SquaredKummerFromSquaredThetas(twistmus);
end function;

TwistPoint := function(P)
    twister := [-1, -1, 1, 1];
	return normalise(C(twister, P));
end function;

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

/*

In what follows we perform a simple scalar-multiplication-based loop to compute a chain of Richelot isogenies on Kummers. We move the input point P through subsequent isogenies and illustrate its order being decreased by a factor of 2 each time. We also push a random point Q through the isogenies. 

This is merely to illustrate that the Kummer approach is compatible with state-of-the-art SIDH implementations. Of course, a real implementation would avoid various checks/normalizations, would work out an optimal binary-tree strategy for the main loop, etc.

See the paper for more details. 

*/


cofactor:=p+1;
repeat
	cofactor:=cofactor div 2;
until IsOdd(cofactor);

N:=((p+1) div 2) div cofactor; //P has exact order N
e:=Factorization(N)[1][2]; //N=2^e

// Q:=	RandomKummerPoint(K);
// assert OnKummer(Q, K);

// TK := TwistKummer(K);
// TQ := TwistPoint(Q);
// assert OnKummer(TQ, TK);


// P:= RandomFullOrderPoint(K);
// P:= KummerScalar(P,K,cofactor); 

// assert #PrimeDivisors(N) eq 1 and IsEven(N);
// assert normalise(KummerScalar(P,K,N)) eq normalise(K[2]);


// for l:=e to 2 by -1 do

// 	P4:=eDBLs(P,K,l-2);
// 	P2:=DBL(P4,K);

// 	mus,pis:=IsogenousSquaredThetasFromTorsionKernel(P2,P4);
// 	P:=IsogenyKummerPoint(P,pis);
// 	Q:=IsogenyKummerPoint(Q,pis);
// 	K:=SquaredKummerFromSquaredThetas(mus);
// 	assert OnKummer(P,K);
// 	assert OnKummer(Q,K);

// end for;

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

"Kummer.m done\n";
