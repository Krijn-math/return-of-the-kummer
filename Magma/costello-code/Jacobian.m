// Copyright (c) Microsoft. All rights reserved.
// Licensed under the MIT license. 

clear;

load "../costello-code/Params.m";

p:=2^18*3^13-1;

/*
This file performs computations as described in Section 4 of the paper. 
*/

alpha,E_alpha,Fp,Fp2<i>,poly<x>:=SupersingularMontgomeryCurve(p);
C_alpha,J_alpha, beta, gamma, zs:=SupersingularAbelianSurfaceFromMontgomeryCurve(alpha);

z1:=zs[1]; z2:=zs[2]; z3:=zs[3]; z4:=zs[4]; z5:=zs[5]; z6:=zs[6];

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

kappa:=function(zi,zj,z)
	
	/*

	Computes the isomorphism kappa between two genus 2 curves C->C', specialized to the instance of computing isomorphic (2,2) kernels as in Section 4 of the paper. As discussed in the paper, the square roots could most likely be replaced by a function of a 4-torsion (or maybe 8-torsion) point lying above the input, like we do on the Kummers.

	INPUTS: - zi,zj in Fp, corresponding to the two-torsion point ((x-zi)*(x-zj),0) on J(C)
			- z, corresponding to the Weierstrass point (z,0) on C. 
	OUTPUTS: - the corresponding isomorphism of the x-coordinate (z,--) described in Section 4. In our case we only apply the isomorphism to the Weierstrass points (z,0) of C. 

	*/

	u1:=-zi-zj;
	u0:=zi*zj;

	d:=1;
	c:=(u0+Sqrt((u0-1)^2+u1^2)-1)/(-u1);
	b:=Sqrt(-u1*(2*u0*c-u1-2*c))/(-u1);
	a:=b*(-c*u1-2*u0)/(u1+2*c);

	return (a*z+b)/(c*z+d);

end function;

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

invariants:=function(C)

	/*

	Computes the 'normalized' Igusa-Clebsch invariants of a genus 2 curve, assuming I[1] ne 0. 

	INPUTS: A genus 2 curve C
	OUTPUTS: A 3-tuple of isomorphism invariants of C

	*/

	I:=IgusaClebschInvariants(C);
	N:=[I[2]/I[1]^2,I[3]/I[1]^3,I[4]/I[1]^5];
	return N;

end function;

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

RichelotIsogeny:=function(splitting)

	/*

	Computes the Richelot (2,2) isogeny of a genus 2 curve/Jacobian who kernel corresponds to a particular quadratic splitting. See Section 4 of the paper.

	INPUTS: - splitting: [G1,G2,G3], all quadratics in Fp[x]
	OUTPUTS: - C': the curve underlying...
			 - J: the (2,2)-isogenous Jacobian
			 - gs: the 6-tuple of field elements in case we want to evaluate the Richelot isogeny on points.

	*/

	G1:=splitting[1];
	G2:=splitting[2];
	G3:=splitting[3];

	g10:=Coefficients(G1)[1]; g11:=Coefficients(G1)[2];
	g20:=Coefficients(G2)[1]; g21:=Coefficients(G2)[2];
	g30:=Coefficients(G3)[1]; g31:=Coefficients(G3)[2];

	H1:=g31*x^2+2*x*g30-g21*x^2+g21*g30-2*x*g20-g20*g31;
	H2:=g11*x^2+2*x*g10-g31*x^2+g31*g10-2*x*g30-g11*g30;
	H3:=g21*x^2+2*x*g20-g11*x^2+g11*g20-2*x*g10-g21*g10;

	delta:=g21*g30-g20*g31+g31*g10-g11*g30+g11*g20-g21*g10;

	if delta ne 0 then
		f:=H1*H2*H3/(-delta);
	else
		f:=H1*H2*H3;
	end if;

	C:=HyperellipticCurve(f);
	J:=Jacobian(C);
	gs:=[g10,g11,g20,g21,g30,g31];

	return C,J,gs;

end function;

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

RichelotIsogenyPoint:=function(splitting,P)

	/*

	Evaluates a Richelot (2,2) isogeny of a genus 2 curve/Jacobian who kernel corresponds to a particular quadratic splitting. See Section 4 of the paper. Can be extended linearly to generic elements of J.

	INPUTS: - splitting: [G1,G2,G3], all quadratics in Fp[x]
		    - P: a point on the input curve C
	OUTPUTS: - C': the curve underlying...
			 - J: the (2,2)-isogenous Jacobian
			 - gs: the 6-tuple of field elements in case we want to evaluate the Richelot isogeny on points.

	*/

	_,J,gs:=RichelotIsogeny(splitting);
	x1:=P[1]; y1:=P[2];
	g10:=gs[1]; g11:=gs[2]; g20:=gs[3]; g21:=gs[4]; g30:=gs[5]; g31:=gs[6];

	u1 := -2*(-x1^2*g20+g11*x1*g30-g11*x1*g20+g10*g30+x1^2*g10+g21*x1*g10-g21*x1*g30-g20*g30)/(x1^2*g21-g11*x1*g31+g21*g10-g31*g10-x1^2*g11+g21*x1*g31+g20*g31-g11*g20);

	u0 := -(x1^2*g21*g30-x1^2*g20*g31-g11*x1*g20*g31+g10*g21*g30+x1^2*g31*g10-x1^2*g11*g30+g21*x1*g31*g10-g20*g11*g30)/(x1^2*g21-g11*x1*g31+g21*g10-g31*g10-x1^2*g11+g21*x1*g31+g20*g31-g11*g20);

	v1:=(x1^2+g11*x1+g10)*(g20+x1^2+g21*x1)*(-g31*g10+g20*g31+g21*g10-g11*g20-g21*g30+g30*g11)*(-4*g20*g30+4*g10*g30-4*g21*x1*g30-4*x1^2*g20-2*x1*g20*g31+g20*g31^2+4*g11*x1*g30-2*g11*x1*g20-g20*g11*g31+4*x1^2*g10+2*g10*g31*x1-g10*g31^2+2*g21*x1*g10+g10*g21*g31-2*g21*x1^3-x1^2*g21*g31+g21*x1*g31^2+2*g11*x1^3+g11*x1^2*g31-g11*g31^2*x1)/((x1^2*g21-g11*x1*g31+g21*g10-g31*g10-x1^2*g11+g21*x1*g31+g20*g31-g11*g20)^2*y1);

	v0:=(x1^2+g11*x1+g10)*(g20+x1^2+g21*x1)*(-g31*g10+g20*g31+g21*g10-g11*g20-g21*g30+g30*g11)*(g21*x1*g31*g10+2*g10*g21*g30+2*x1^2*g31*g10+g10*g31^2*x1-g21*x1^3*g31+2*x1^2*g21*g30-x1^2*g31^2*g21-2*g20*g11*g30+x1^3*g11*g31-2*x1^2*g20*g31+g11*g31^2*x1^2-x1*g20*g31^2-2*x1^2*g11*g30-g11*x1*g20*g31)/((x1^2*g21-g11*x1*g31+g21*g10-g31*g10-x1^2*g11+g21*x1*g31+g20*g31-g11*g20)^2*y1);

	return J![x^2+u1*x+u0,v1*x+v0];

end function;

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

/*
Below we compute the Richelot (2,2)-isogenies whose kernels correspond to the three quadratic splittings in Lemma 2 of the paper. 
*/

assert z3 eq -z2; assert z4 eq -1/z1; assert z5 eq -1/z2; assert z6 eq 1/z2;

G23:=(x-z3)*(x-z2); G56:=(x-z5)*(x-z6); G14:=(x-z1)*(x-z4);
G45:=(x-z4)*(x-z5); G12:=(x-z1)*(x-z2); G36:=(x-z3)*(x-z6);
G16:=(x-z1)*(x-z6); G34:=(x-z3)*(x-z4); G25:=(x-z2)*(x-z5);

splitting_O:=[G23,G56,G14];
splitting_U:=[G45,G12,G36];
splitting_UU:=[G16,G34,G25];


CO,JO:=RichelotIsogeny(splitting_O);
invsO:=invariants(CO);
assert RichelotIsogenyPoint(splitting_O,Random(C_alpha)) in JO;
assert ((p+1))*Random(JO) eq JO!0;

CU,JU:=RichelotIsogeny(splitting_U);
invsU:=invariants(CU);
assert ((p+1))*Random(JU) eq JU!0;

CUU,JUU:=RichelotIsogeny(splitting_UU);
invUU:=invariants(CUU);
assert ((p+1))*Random(JUU) eq JUU!0;

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

/*

In what follows we illustrate the isomorphisms discussed at the end of Section 4. 

We start by supposing the 2-torsion point we encounter in an SIDH computation is ((x-z4)*(x-z5),0) in J(C), so we are in the splitting U. We input it into kappa to transform the splitting into one which resembles O, but is on an isomorphic Jacobian J(C'), call it O'. We then compute the Richelot isogeny with kernel O' from J(C'), and show that the invariants of the resulting curve are the same as the curve underlying J/U. 

*/

v:=[z4,z5];

Z2:=kappa(v[1],v[2],z4); Z3:=kappa(v[1],v[2],z5);
Z5:=kappa(v[1],v[2],z1); Z6:=kappa(v[1],v[2],z2);
Z1:=kappa(v[1],v[2],z3); Z4:=kappa(v[1],v[2],z6);

assert Z3 eq -Z2; assert Z4 eq -1/Z1; assert Z5 eq -1/Z2; assert Z6 eq 1/Z2;

G23:=(x-Z3)*(x-Z2); G56:=(x-Z5)*(x-Z6); G14:=(x-Z1)*(x-Z4);
G45:=(x-Z4)*(x-Z5); G12:=(x-Z1)*(x-Z2); G36:=(x-Z3)*(x-Z6);
G16:=(x-Z1)*(x-Z6); G34:=(x-Z3)*(x-Z4); G25:=(x-Z2)*(x-Z5);

COkapU1,JOkapU1:=RichelotIsogeny([G23,G56,G14]);

invsOkapU1:=invariants(COkapU1);
assert ((p+1))*Random(JOkapU1) eq JOkapU1!0;

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

/*

Here we do the exact same as above but now with the splitting ((x-z1)*(x-z6),0) in J(C), which corresponds to UU. The same thing can be done with the splittings G_{1,2} and G_{3,4} (see Lemma 2), with roots labelled so that the assertions below are satisfied.

*/
v:=[z1,z6];

Z2:=kappa(v[1],v[2],z1); Z3:=kappa(v[1],v[2],z6);
Z5:=kappa(v[1],v[2],z4); Z6:=kappa(v[1],v[2],z3);
Z1:=kappa(v[1],v[2],z2); Z4:=kappa(v[1],v[2],z5);

assert Z3 eq -Z2; assert Z4 eq -1/Z1; assert Z5 eq -1/Z2; assert Z6 eq 1/Z2;

G23:=(x-Z3)*(x-Z2); G56:=(x-Z5)*(x-Z6); G14:=(x-Z1)*(x-Z4);
G45:=(x-Z4)*(x-Z5); G12:=(x-Z1)*(x-Z2); G36:=(x-Z3)*(x-Z6);
G16:=(x-Z1)*(x-Z6); G34:=(x-Z3)*(x-Z4); G25:=(x-Z2)*(x-Z5);

COkapU2,JOkapU2:=RichelotIsogeny([G23,G56,G14]);

insOkapU2:=invariants(COkapU2);
assert ((p+1))*Random(JOkapU2) eq JOkapU2!0;

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

// "done";
