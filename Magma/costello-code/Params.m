// Copyright (c) Microsoft. All rights reserved.
// Licensed under the MIT license. 

p := 2^246*3*67 - 1;
f2 := Valuation(p+1, 2);
printf "using prime p := %o - 1\n\n", Factorization(p + 1);

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

SupersingularMontgomeryCurve:= function(p)

	/*
	This function computes a supersingular Montgomery curve by taking at least 10 random 2-isogenies in the supersingular isogeny graph. 


	INPUTS: - p: a prime (assumed to be of the form p=2^eA*3^eB-1)
	OUTPUTS: - alpha: non-zero, corresponds to 2-torsion point (alpha,0) on E_alpha 
			 - E_alpha: supersingular Montgomery curve E_alpha: y^2=x*(x-alpha)*(x-1/alpha)
			 - Fp: Underlying base field
			 - Fp2: Underlying quadratic extension field
			 - poly: Polynomial ring over Fp2
	*/
	assert IsPrime(p: Proof:=false); //and #Factorization(p+1) eq 2 and Factorization(p+1)[2][1] eq 3;
	Fp:=GF(p);
	Fp2<i>:=ExtensionField<Fp,x|x^2+1>;
	poly<x>:=PolynomialRing(Fp2);

 	alpha:=i; 											//starting 2-torsion point (i,0) on E_alpha: y^2=x^3+x
 	E_alpha:=EllipticCurve(x*(x-alpha)*(x-1/alpha));
 	assert (p+1)*Random(E_alpha) eq E_alpha!0;
 	
 	for j:=1 to 10 do
			alpha:=2*alpha^2-1+Random([-1,1])*2*alpha*Sqrt(alpha^2-1);  //compute isogenous alpha
	end for;

	E_alpha:=EllipticCurve(x*(x-alpha)*(x-1/alpha));
	
	while jInvariant(E_alpha) in Fp do				  // do not want a subfield curve
		alpha:=2*alpha^2-1+Random([-1,1])*2*alpha*Sqrt(alpha^2-1);
		E_alpha:=EllipticCurve(x*(x-alpha)*(x-1/alpha));
	end while;

	assert (p+1)*Random(E_alpha) eq E_alpha!0;

	return alpha,E_alpha,Fp,Fp2,poly;

end function;

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

SupersingularAbelianSurfaceFromMontgomeryCurve:=function(alpha)

	/*
	This function computes the supersingular abelian surface over Fp corresponding to a supersingular Montgomery elliptic curve E_alpha over Fp2.


	INPUTS: - alpha: a non-zero abscissa of a 2-torsion point defining E_alpha
	OUTPUTS: - C_alpha: a genus 2 hyperelliptic curve of the form C: y^2=\Pi (x-z_i), i=1..6
			 - J_alpha: the abelian surface that is the Jacobian of C_alpha
			 - beta, gamma: constants defined in the paper
			 - zs: the z_i, i.e., the six roots of the sextic hyperelliptic polynomial
	*/

	beta:=Sqrt((alpha^2-1)/alpha);					// See Section 3 of the paper
	gamma:=Sqrt(alpha);

	beta0:=ElementToSequence(beta)[1];				
	beta1:=ElementToSequence(beta)[2];				
	gamma0:=ElementToSequence(gamma)[1];
	gamma1:=ElementToSequence(gamma)[2];

	z1:=beta0/beta1; 
	z2:=gamma0/gamma1; 
	z3:=-gamma0/gamma1; 
	z4:=-beta1/beta0; 
	z5:=-gamma1/gamma0; 
	z6:=gamma1/gamma0;

	zs:=[z1,z2,z3,z4,z5,z6];

	//curve/Jacobian defined over Fp
	Fp:=BaseField(Parent(alpha));
	_<x>:=PolynomialRing(Fp);
	C_alpha:=HyperellipticCurve((x-z1)*(x-z2)*(x-z3)*(x-z4)*(x-z5)*(x-z6));
	J_alpha:=Jacobian(C_alpha);

	return C_alpha, J_alpha, beta, gamma, zs;

end function;

///////////////////////////////////////////////////////////////
//////// Useful functions for fast Kummer arithmetic //////////
///////////////////////////////////////////////////////////////

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
	assert K_G eq (mu1^2-mu2^2+mu3^2-mu4^2)/(mu1*mu3-mu2*mu4);
	K_H:=(mu1^2+mu2^2-mu3^2-mu4^2)/(mu1*mu2-mu3*mu4);
	K_F:=4*K_F^2*mu1*mu2*mu3*mu4;

	K1:=[K_F,K_G,K_H];
	K2:=thetas;
	K3,K4:=KummerConstantsFromSquaredThetas(thetas);

	return [K1,K2,K3,K4];

end function;

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

SupersingularKummerSurfaceFromMontgomeryCurve:=function(alpha)
	
	/*

	Computes the set of supersingular Kummer surface parameters corresponding to a given supersingular Montgomery curve

	INPUTS: - alpha: a non-zero abscissa of a 2-torsion point defining E_alpha
	OUTPUTS: - the full set of Kummer surface parameters defined in SquaredKummerFromSquaredThetas

	*/

	beta:=Sqrt((alpha^2-1)/alpha);				// See Section 3
	gamma:=Sqrt(alpha);

	b0:=ElementToSequence(beta)[1];
	b1:=ElementToSequence(beta)[2];
	g0:=ElementToSequence(gamma)[1];
	g1:=ElementToSequence(gamma)[2];
	
	lambda:=-(b0*g1+b1*g0)*(b0*g0+b1*g1)/((b0*g0-b1*g1)*(b0*g1-b1*g0));

	mu1:=(g0-g1)*(g0+g1)/(g0^2+g1^2)*Sqrt(lambda);	// See Section 5
	mu2:=(g0-g1)*(g0+g1)/(g0^2+g1^2)/Sqrt(lambda); 
	mu3:=1; mu4:=1;

	thetas:=[mu1,mu2,mu3,mu4];

	return SquaredKummerFromSquaredThetas(thetas);

end function;

MinSupersingularKummerSurfaceFromMontgomeryCurve:=function(alpha)
	
	/*

	Computes the set of supersingular Kummer surface parameters corresponding to a given supersingular Montgomery curve

	INPUTS: - alpha: a non-zero abscissa of a 2-torsion point defining E_alpha
	OUTPUTS: - the full set of Kummer surface parameters defined in SquaredKummerFromSquaredThetas

	*/

	beta:=Sqrt((alpha^2-1)/alpha);				// See Section 3
	gamma:=Sqrt(alpha);

	b0:=ElementToSequence(beta)[1];
	b1:=ElementToSequence(beta)[2];
	g0:=ElementToSequence(gamma)[1];
	g1:=ElementToSequence(gamma)[2];
	
	lambda:=-(b0*g1+b1*g0)*(b0*g0+b1*g1)/((b0*g0-b1*g1)*(b0*g1-b1*g0));

	tmp := -Sqrt(lambda);

	mu1:=(g0-g1)*(g0+g1)/(g0^2+g1^2)*tmp;	// See Section 5
	mu2:=(g0-g1)*(g0+g1)/(g0^2+g1^2)/tmp; 
	mu3:=1; mu4:=1;

	thetas:=[mu1,mu2,mu3,mu4];

	return SquaredKummerFromSquaredThetas(thetas);

end function;

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////


EverythingFromMontgomeryCurve := function(alpha)

	/*

	Computes the set of supersingular Kummer surface parameters corresponding to a given supersingular Montgomery curve

	INPUTS: - alpha: a non-zero abscissa of a 2-torsion point defining E_alpha
	OUTPUTS: - C_alpha: a genus 2 hyperelliptic curve of the form C: y^2=\Pi (x-z_i), i=1..6
			 - J_alpha: the abelian surface that is the Jacobian of C_alpha
			 - beta, gamma: constants defined in the paper
			 - zs: the z_i, i.e., the six roots of the sextic hyperelliptic polynomial
			 - the full set of Kummer surface parameters defined in SquaredKummerFromSquaredThetas

	*/

	beta:=Sqrt((alpha^2-1)/alpha);				// See Section 3
	gamma:=Sqrt(alpha);

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

	zs:=[z1,z2,z3,z4,z5,z6];

	//curve/Jacobian defined over Fp
	Fp:=BaseField(Parent(alpha));
	_<x>:=PolynomialRing(Fp);
	C_alpha:=HyperellipticCurve((x-z1)*(x-z2)*(x-z3)*(x-z4)*(x-z5)*(x-z6));
	J_alpha:=Jacobian(C_alpha);

	
	lambda:=-(b0*g1+b1*g0)*(b0*g0+b1*g1)/((b0*g0-b1*g1)*(b0*g1-b1*g0));

	mu1:=(g0-g1)*(g0+g1)/(g0^2+g1^2)*Sqrt(lambda);	// See Section 5
	mu2:=(g0-g1)*(g0+g1)/(g0^2+g1^2)/Sqrt(lambda); 
	mu3:=1; mu4:=1;

	thetas:=[mu1,mu2,mu3,mu4];

	K := SquaredKummerFromSquaredThetas(thetas);

	return C_alpha, J_alpha, beta, gamma, zs, K;

end function;

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
/* 
	We add the code below to initialise the Hyperelliptic Curves, Jacobians 
	and Kummer surfaces used in all the files
*/

// Setting up Montgomery curve E_{\alpha}, and finite fields Fp, Fp2
alpha, E_alpha, Fp, Fp2<i>, poly := SupersingularMontgomeryCurve(p);
// Setting up the Hyperelliptic curve and Jacobian associated to E_{\alpha}
C_alpha, J_alpha, beta, gamma, zs := SupersingularAbelianSurfaceFromMontgomeryCurve(alpha);
// Setting up the elliptic Kummer surface associated to E_{\alpha}
K := SupersingularKummerSurfaceFromMontgomeryCurve(alpha);

PX<X> := PolynomialRing(Fp);
poly<x>:=PolynomialRing(Fp2);


// Setting up important constants needed throught (see Section 3 of eprint/2018/850)
r1:=(alpha-1/alpha)^(p-1); r2:=alpha^(p-1); r3:=1/alpha^(p-1);
betahat:=Sqrt(r3-r2);
w:=Sqrt((r2-1)^2*(1-r1)*r3);

// Curves/Jacobian defined over Fp2
Etil_alpha:=EllipticCurve((x-Fp2!r1)*(x-Fp2!r2)*(x-Fp2!r3));
Ctil_alpha:=HyperellipticCurve((x^2-r1)*(x^2-r2)*(x^2-r3));
Jtil_alpha:=Jacobian(Ctil_alpha);


// Initialising Twists of curves
A := Coefficients(E_alpha)[2];
twist_alpha := Roots(x^2 - A*x + 1)[1][1];
C_twist, J_twist, beta_twist, gamma_twist, zs_twist := SupersingularAbelianSurfaceFromMontgomeryCurve(twist_alpha);
K_twist := SupersingularKummerSurfaceFromMontgomeryCurve(twist_alpha);

"Curves initialized\n";
