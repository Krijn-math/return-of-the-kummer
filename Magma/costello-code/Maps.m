// Copyright (c) Microsoft. All rights reserved.
// Licensed under the MIT license. S

/*
This file computes the back-and-forth maps between (the Weil restriction of) a given supersingular Montgomery curve over GF(p^2) and the corresponding abelian surface over GF(p), as described in Section 3 of the paper:  
        ' Computing supersingular isogenies on Kummer surfaces ' by Craig Costello (eprint/2018/850)

The full maps (eta: E_alpha(Fp2)->J_alpha(Fp) and eta_hat: J_alpha(Fp)-> E_alpha(Fp2)) 
are given at the very bottom.
*/

///////////////////////////////////////////////////////////////
/////////////////////// psi and psi_inv ///////////////////////
///////////////////////////////////////////////////////////////

psi:=function(P) //isomorphism from E_alpha to Etil_alpha
	assert P in E_alpha;
	x:=P[1]; y:=P[2];
	return Etil_alpha![(betahat/beta)^2*x+r1,(betahat/beta)^3*y];
end function;

assert psi(Random(E_alpha)) in Etil_alpha;

psi_inv:=function(P) //isomorphism from Etil_alpha to E_alpha 
	assert P in Etil_alpha;
	x:=P[1]; y:=P[2];
	return E_alpha![(beta/betahat)^2*(x-r1),(beta/betahat)^3*y];
end function;

assert psi_inv(Random(Etil_alpha)) in E_alpha;

///////////////////////////////////////////////////////////////
/////////////////////// phi and phi_inv ///////////////////////
///////////////////////////////////////////////////////////////

phi:=function(P) //map from Ctil_alpha(Fp2) to C_alpha(Fp2)
	assert P in Ctil_alpha;
	x:=P[1]; y:=P[2];
	return BaseChange(C_alpha,Fp2)![-i*(x-1)/(x+1),y/w*(1-(x-1)/(x+1))^3];
end function;

assert phi(Random(Ctil_alpha)) in BaseChange(C_alpha,Fp2);

phi_inv:=function(P) //map from C_alpha(Fp2) to Ctil_alpha(Fp2)
	assert P in BaseChange(C_alpha,Fp2);
	x:=P[1]; y:=P[2];
	return Ctil_alpha![-(x-i)/(x+i),-i*y*w/(x+i)^3];
end function;

assert phi_inv(Random(BaseChange(C_alpha,Fp2))) in Ctil_alpha;

///////////////////////////////////////////////////////////////
///////////////////////      omega      ///////////////////////
///////////////////////////////////////////////////////////////

omega:=function(P) //Scholten's "obvious map" from Ctil_alpha to Etil_alpha
	assert P in Ctil_alpha;
	x:=P[1]; y:=P[2];
	return Etil_alpha![x^2,y];
end function;

assert omega(Random(Ctil_alpha)) in Etil_alpha;

///////////////////////////////////////////////////////////////
/////////////////////// rho and rho_hat ///////////////////////
///////////////////////////////////////////////////////////////

rho:=function(P) //map from Etil_alpha(Fp2) to J_alpha(Fp2)
	assert P in Etil_alpha;
	xtil:=P[1]; ytil:=P[2];
	u1:=2*i*(xtil+1)/(xtil-1);
	u0:=-1;
	v1:=-4*i*ytil*(xtil+3)/(w*(xtil-1)^2);
	v0:=4*ytil/(w*(xtil-1));
	return BaseChange(J_alpha,Fp2)![x^2+u1*x+u0,v1*x+v0];
end function;

assert rho(Random(Etil_alpha)) in BaseChange(J_alpha,Fp2);

rho_hat:=function(P) //map from J_alpha(Fp2) to Etil_alpha(Fp2) X Etil_alpha(Fp2)
	assert P in J_alpha;
	assert Degree(P[1]) eq 2;
	poly<x>:=PolynomialRing(Fp2);
	u:=poly!P[1]; v:=poly!P[2];

	x1:=Roots(u)[1][1]; y1:=Evaluate(v,x1);
	P1:=BaseChange(C_alpha,Fp2)![x1,y1];

	if #Roots(u) eq 2 then
		x2:=Roots(u)[2][1]; y2:=Evaluate(v,x2);
		P2:=BaseChange(C_alpha,Fp2)![x2,y2];
	else
		P2 := P1;
	end if;

	return [omega(phi_inv(P1)),omega(phi_inv(P2))];
end function;

repeat
	P:=Random(J_alpha);
until Degree(P[1]) eq 2;

assert rho_hat(P)[1] in Etil_alpha and rho_hat(P)[2] in Etil_alpha;

///////////////////////////////////////////////////////////////
///////////////////////// Trace map ///////////////////////////
///////////////////////////////////////////////////////////////

Tr:=function(P)	//map from J_alpha(Fp2) down to J_alpha(Fp)
	assert P in BaseChange(J_alpha,Fp2);
	sigP:=Frobenius(P,Fp);
	return J_alpha!(P+sigP);
end function;

repeat
	P:=Random(BaseChange(J_alpha,Fp2));
until Degree(P[1]) eq 2 and Degree(P[2]) eq 1;

assert Tr(P) in J_alpha;

///////////////////////////////////////////////////////////////
///////////////// addition on Etil_alpha //////////////////////
///////////////////////////////////////////////////////////////

oplus_Etil:=function(pts) //addition law on Etil_alpha (Magma's built in)
	assert pts[1] in Etil_alpha;
	assert pts[2] in Etil_alpha;
	return pts[1]+pts[2]; 
end function;

assert oplus_Etil([Random(Etil_alpha),Random(Etil_alpha)]) in Etil_alpha;

///////////////////////////////////////////////////////////////
/////////////////////// eta and eta_hat ///////////////////////
///////////////////////////////////////////////////////////////

eta:=function(P) //composition map from E_alpha(Fp2) to J_alpha
	assert P in E_alpha;
	return Tr(rho(psi(P)));
end function;

assert eta(Random(E_alpha)) in J_alpha;

eta_hat:=function(P) //composition map from J_alpha to E_alpha(Fp2)
	assert P in J_alpha;
	return psi_inv(oplus_Etil(rho_hat(P)));
end function;

assert eta_hat(Random(J_alpha)) in E_alpha;


