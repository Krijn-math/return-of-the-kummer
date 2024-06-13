// this file is here only for historical and honesty reasons
// we wanted to have the fakely generated signature properly verify
// we did so by ensureing that the "message" actually matches up to what was computed
// that is, we get a random point Qdual and want to express it as a combination P + sQ
// and then provide s as the message, so that it properly verifies
// this s is used in the python code in the end

"trying to compress signature thing";

p := 2^246*3*67 - 1;
f2 := Valuation(p+1, 2);
cofac := 3*67;

Fp := FiniteField(p);
Fp2<i> := FiniteField(p^2);
poly<x> := PolynomialRing(Fp);
poly2<X> := PolynomialRing(Fp2);

//setting up the right values for our fake signature

K := [[3976264865455431127163152623044725221074656212446808780353317313557596481164, 15040261800872891414401279150725890220154184782881821607211164992018860381013, 18510330634255535481503740278782457626756034706526281943094509717069409807974], [10122373594264625858287459231068308720793591784808500401674763057006765388087, 4917888206608265556113819919657581499360592998073321205536401935012094992926, 1, 1], [17804215759035486409710709256158235869948061903070651314944878593374462496039, 2583133077710062553060332442658596522212293580123830376670054399794942121299, 2627199597303635686968734378852119135128801730915306529458544370121003759303, 2627199597303635686968734378852119135128801730915306529458544370121003759303], [19086078152051451073656364506933166365410737413951306807659700335140753054701, 19183477418993823160788483863036048294784089536825543549511187568321164345011, 16059100767167443881571067077170786218161236237479129950977624543690542578822, 16059100767167443881571067077170786218161236237479129950977624543690542578822]];
ros := [Fp!r : r in [17880428715822195577778142111226566764933794395220211673497465197404629143696, 15372785572458329206902634075503039147794180774359325601904212542722634596122, 9998398001757335054721758020485003335227068788616012578777719339891979114736]];
P := [Fp!p : p in [4432004840680056097753277308769468303916539573337126552165973178055060307710, 440958774389177853966659722142751741178633896554051094863661611823077393280, 21216763796355192803895049980625871882914766542828034405613528129827147442390, 1]];
Q := [Fp!p : p in [18719425469072506849701796885875583329274492452884270403615999363683350572879, 11171002343523255142050865446496101812172345823747085411275610309236606282204, 2283833963664284026818222908609024577770386765554634079265801374900863349460, 1]];
Qdual := [Fp!p : p in [5694286680578755948377802206675662741557196445631985742624785491161050193519, 11377637559926572112474133334898429435427376305664551708940131317098789733315, 2510225345018105602991291142356552393182649453020322772362730199240041740970, 17938606053097126506951554152487666580526228221839919799400292167388877944987]];

for i in [1..4] do K[i] := [Fp!k : k in K[i]]; end for;

wp := [0, 0, 1] cat ros;
w1, w2, w3, w4, w5, w6 := Explode(wp);

C_rosenhain := HyperellipticCurve(x*(x-1)*&*[x - r : r in ros]);
J_rosenhain := Jacobian(C_rosenhain);

// had to copy everything here because of the way the Magma folders are structured
// this is very unelegant, but the meat is on the bottom of this file

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

assert OnKummer(P, K);
assert OnKummer(Q, K);

assert KummerScalar(P, K, 2^(f2-3)) ne K[2];
assert KummerScalar(Q, K, 2^(f2-3)) ne K[2];
assert KummerScalar(Qdual, K, 2^(f2-3)) ne K[2];

///////////////////////////////////////////////////////////////
////////                                             //////////
////////           New approach K --> J              //////////
////////                                             //////////
///////////////////////////////////////////////////////////////

function CorrectPoint(P, K)
    return [P[i]/K[2][i] : i in [1..4]];
end function;

function GetU_helper(P, K)
    X := CorrectPoint(P, K);

    //all the below should be equal to v0^2
    //ff := [ fi[i] - lambda*X[i] : i in [1..4]];

    u0_top := ((w3 - w5)*w4*w6*X[1] + (w4 - w6)*w3*w5*X[2] - (w3 - w6)*w4*w5*X[3] - (w4 - w5)*w3*w6*X[4]);
    u0_bot := (w4 - w6)*X[1] + (w3 - w5)*X[2] - (w4 - w5)*X[3] - (w3 - w6)*X[4];
    u1_top := -(X[1] + X[2] - X[3] - X[4])*(w3*w4 - w5*w6);
    u1_bot := u0_bot;

    return u0_top, u0_bot, u1_top, u1_bot, X[1];
end function;

function GetU(P, K)
    u0_top, u0_bot, u1_top, u1_bot := GetU_helper(P, K);

    u0 := u0_top/u0_bot;
    u1 := u1_top/u1_bot;

    return u0, u1;
end function;

function Getvo2(P, K)
    u0_top, u0_bot, u1_top, u1_bot, X1 := GetU_helper(P, K);

    u0 := u0_top/u0_bot;
    u1 := u1_top/u1_bot;

    lambda_top := -(w3 - w4)*(w5 - w6)*(w3*w4 - w5*w6)*u0_top;
    lambda_bot := u0_bot^2;
    lambda := lambda_top/lambda_bot;

    //manual evaluation in fi[1] - lambda*X[1]
    if DBL(P, K) ne K[2] then
        v02 := u0*(w3*w5 - u0)*(w4 + w6 + u1) - lambda*X1;
        return u0, u1, v02;
    end if;

    return u0, u1, 0;
end function;

function JacPointAbove(P)
    //this map should be in a different file probably
    u0, u1, v02 := Getvo2(P, K);

    poly<x> := PolynomialRing(Fp);
    ax := x^2 + u1*x + u0;
    possible := SetToSequence(Points(J_rosenhain, ax, 2));
    filter_possible := [ D : D in possible | Coefficients(D[2])[1]^2 eq v02 ];
    //assert {P} eq {normalise(RosenhainToKummer(D, ros, K)) : D in filter_possible};

    return filter_possible[1];
end function;


// HyperEll curve function
function WorkDiscLog(R, P, Q, ell, ord)
    //we use this now by mapping points from kummer to jac
    if ord eq 1 then
        for a,b in [0..ell] do
            Rp := a*P + b*Q;
            if R eq Rp then return a,b; end if;
        end for;
        print "error";
        assert 3 eq 5;
    end if;

    e := ord div 2;
    fac1 := ell^(ord - e);
    P1 := fac1*P; Q1 := fac1*Q; R1 := fac1*R;
    a1, b1 := WorkDiscLog(R1, P1, Q1, ell, e);

    fac2 := ell^(e);
    P2 := fac2*P; Q2 := fac2*Q; R2 := R - a1*P - b1*Q;
    a2, b2 := WorkDiscLog(R2, P2, Q2, ell, ord - e);

    // a1; a2;
    return a1 + a2*ell^e, b1 + b2*ell^e;
end function;

//Ell curve function
function DiscLog(R, P, Q, ell, ord)
    a, b := WorkDiscLog(R, P, Q, ell, ord);
    a := a mod ell^ord;
    b := b mod ell^ord;
    assert R eq a*P + b*Q;
    return a, b;
end function;


//we simply raise P, Q and Qdual to the Jacobian above
//then we compute the values a and b there

JP := JacPointAbove(P);
JQ := JacPointAbove(Q);
JR := JacPointAbove(Qdual);
a, b := DiscLog(JR, JP, JQ, 2, f2-1);

assert JR eq a*JP + b*JQ;

assert a eq 46720790296147925252012331917861943021250115703078123560917607415510761134;
assert b eq 30907223338725842147573934659555441642681283691210078451500931625457094026;
