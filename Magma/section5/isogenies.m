/*
    This file contains functions that describe the (2,2)-isogenies between Kummer surfaces given in Section 5
*/


////////////////////////////////////
////////////// SET-UP //////////////
////////////////////////////////////

p:=2^13*3^7-1;
Fp:=GF(p);
Fp2<i>:=ExtensionField<Fp,x|x^2+1>;
_<x> := PolynomialRing(Fp2);

load "functions.m";

// We set-up a (psuedo-)random superspecial Kummer surface, which is therefore defined over Fp2. 
C:=HyperellipticCurve(x^6+1);
C:=random_walk(C);
K,rosen:=KummerFromCurve(C);
C:=HyperellipticCurve(x*(x-1)*(x-rosen[1])*(x-rosen[2])*(x-rosen[3]));
J:=Jacobian(C);

// Our choice of prime ensures we have rational 4-torsion so our isogenies will also be defined over Fp2
repeat
    repeat
        repeat
            R:=((p+1) div 4)*Random(J);
        until 4*R eq J!0 and 2*R ne J!0 and R ne J!0;
        repeat
            S:=((p+1) div 4)*Random(J);
        until 4*S eq J!0 and 2*S ne J!0 and S notin [J!0,R,-R];
        RpS:= R+S;
    until 4*(RpS) eq J!0 and 2*RpS ne J!0 and RpS notin [J!0,R,-R, S, -S];
until WeilPairing(R,S,4) eq 1;
RpS:= R+S;

// Pushing the points down to the squared Kummer surface 
R4:=JtoSquaredK(R,rosen,K);
S4:=JtoSquaredK(S,rosen,K);
RpS4:=JtoSquaredK(RpS,rosen,K);
O_sq := Squaring(K[2]);
R := DBL(R4, O_sq);
S := DBL(S4, O_sq);
RpS := DBL(RpS4, O_sq);

// Assert that R, S, R+S are 2-torsion points
assert normalise(R) ne normalise(O_sq);
assert normalise(S) ne normalise(O_sq);
assert normalise(RpS) ne normalise(O_sq);


PP<X,Y,Z,T> := PolynomialRing(Fp2,4);

/////////////////////////
//// GETTING SCALING ////
/////////////////////////

function KernelIndex(P, Q, PpQ, P4, Q4, PpQ4, O_sqr)
    /*
        Detects which kernel we are working with (in terms of their ordering in Section 5 of the paper accompanying the code)
        and outputs the corresponding scaling needed for the (2,2)-isogeny (i.e., outputs [1/A:1/B:1/C:1/D]).

        INPUTS: points P, Q generating the kernel
                P4, the 4-torsion point lying above P
                Q4, the 4-torsion point lying above Q

        OUTPUTS: ind, kernel index corresponding to the ordering in Section 5 of the paper 
                 scals, scaling needed to compute the (2,2)-isogeny
    */

    a2,b2,c2,d2 := Explode(O_sqr);
    
    Fp2 := Parent(O_sqr[1]);
    
    check := [&*P eq 0, &*Q eq 0, &*PpQ eq 0];
    N_zerocoord := #[f : f in check | f]; // Checking how many 2 tors with 0 coords are in the kernel

    
    if N_zerocoord eq 0 then 
        scals := Invert4Constants(Hadamard(O_sqr));
        return 1, scals;
    end if;

    points := [normalise(P), normalise(Q), normalise(PpQ)];
    tors4 := [P4,Q4,PpQ4];

    if N_zerocoord eq 2 then 
        "For these cases, we must take square roots...";
        scals := [Sqrt(Fp2!s) : s in Invert4Constants(Hadamard(O_sqr))];
        // We can remove one of these squareroots
        if normalise([ b2, a2, d2, c2 ]) in points then 
            L := Remove(points, Index(points, normalise([ b2, a2, d2, c2 ])));
            if L[1][4] eq 0 then 
                return 2, scals;
            else 
                return 3, scals;
            end if;
        elif normalise([ c2, d2, a2, b2 ]) in points then 
            L := Remove(points, Index(points, normalise([ c2, d2, a2, b2 ])));
            if L[1][4] eq 0 then 
                return 4, scals;
            else 
                return 5, scals;
            end if;
        elif normalise([ d2, c2, b2, a2 ]) in points then 
            L := Remove(points, Index(points, normalise([ d2, c2, b2, a2 ])));
            if L[1][3] eq 0 then 
                return 6, scals;
            else 
                return 7, scals;
            end if;
        else
            "Hmm, some problem..";
        end if;


    elif N_zerocoord eq 3 then 
        "No squareroots needed...";
        nonzero := [[Index(p,v) : v in p | v ne 0] : p in points];
        
        if [1,2] in nonzero and [1,3] in nonzero and [1,4] in nonzero then
            list := []; 
            Append(~list, Hadamard(tors4[Index(nonzero, [1,2])]));
            Append(~list, Hadamard(tors4[Index(nonzero, [1,3])]));
            Append(~list, Hadamard(tors4[Index(nonzero, [1,4])]));
            scals:= Invert4Constants([1,list[1][2]/list[1][1], list[2][3]/list[2][1], list[1][4]*list[2][3]/(list[1][3]*list[2][1])]);
            points_can := [normalise(FourWayMult(Hadamard(X), scals)) : X in points];
            O := FourWayMult(Hadamard(O_sq), scals);
            a,b,c,d := Explode(O);
            if normalise([ b, a, d, c ]) in points_can then 
                return 8, scals;
            else 
                return 10, scals;
            end if;
        elif [1,2] in nonzero and [2,4] in nonzero and [2,3] in nonzero then
            list := []; 
            Append(~list, Hadamard(tors4[Index(nonzero, [1,2])]));
            Append(~list, Hadamard(tors4[Index(nonzero, [2,4])]));
            Append(~list, Hadamard(tors4[Index(nonzero, [2,3])]));
            scals:= Invert4Constants([1,list[1][2]/list[1][1], -i*list[2][3]/list[2][1], -i*list[1][4]*list[2][3]/(list[1][3]*list[2][1])]);
            
            points_can := [normalise(FourWayMult(Hadamard(X), scals)) : X in points];
            O := FourWayMult(Hadamard(O_sq), scals);
            a,b,c,d := Explode(O);
            if normalise([ b, a, d, c ]) in points_can then 
                return 9, scals;
            else 
                return 11, scals;
            end if;
        elif [3,4] in nonzero and [1,3] in nonzero and [2,3] in nonzero then
            list := []; 
            Append(~list, Hadamard(tors4[Index(nonzero, [3,4])]));
            Append(~list, Hadamard(tors4[Index(nonzero, [1,3])]));
            Append(~list, Hadamard(tors4[Index(nonzero, [2,3])]));
            scals:= Invert4Constants([1,-i*list[1][2]/list[1][1], list[2][3]/list[2][1], -i*list[1][4]*list[2][3]/(list[1][3]*list[2][1])]);
            
            points_can := [normalise(FourWayMult(Hadamard(X), scals)) : X in points];
            O := FourWayMult(Hadamard(O_sq), scals);
            a,b,c,d := Explode(O);
            if normalise([ b, -a, d, -c ]) in points_can then 
                return 12, scals;
            else 
                return 14, scals;
            end if;
        elif [3,4] in nonzero and [2,4] in nonzero and [1,4] in nonzero then
            list := []; 
            Append(~list, Hadamard(tors4[Index(nonzero, [3,4])]));
            Append(~list, Hadamard(tors4[Index(nonzero, [2,4])]));
            Append(~list, Hadamard(tors4[Index(nonzero, [1,4])]));
            scals:= Invert4Constants([1,-i*list[1][2]/list[1][1], -i*list[2][3]/list[2][1], list[1][4]*list[2][3]/(list[1][3]*list[2][1])]);
            
            points_can := [normalise(FourWayMult(Hadamard(X), scals)) : X in points];
    
            O := FourWayMult(Hadamard(O_sq), scals);
            a,b,c,d := Explode(O);
            if normalise([ b, -a, d, -c ]) in points_can then 
                return 13, scals;
            else 
                return 15, scals;
            end if;
        else
            return 0, "Hmm there is some problem..";
        end if;
    end if;

end function;

///////////////////////////
//// GETTING ALPHA MAP ////
///////////////////////////

// These are the linear map "alpha" for each kernel. 
// Here the i-th map in the list corresponds to the i-th kernel as per the index given by KernelIndex()
AA := [[[PP | 1,0,0,0], [PP | 0,1,0,0], [PP | 0,0,1,0], [PP | 0,0,0,1]],
    [[PP | 1,1,0,0], [PP | 1,-1,0,0], [PP | 0,0,1,1], [PP | 0,0,1,-1]],
    [[PP | 1,i,0,0], [PP | 1,-i,0,0], [PP | 0,0,1,i], [PP | 0,0,1,-i]],
    [[PP | 1,0,1,0], [PP | 1,0,-1,0], [PP | 0,1,0,1], [PP | 0,1,0,-1]],
    [[PP | 1,0,i,0], [PP | 1,0,-i,0], [PP | 0,1,0,i], [PP | 0,1,0,-i]],
    [[PP | 1,0,0,1], [PP | 1,0,0,-1], [PP | 0,1,1,0], [PP | 0,1,-1,0]],
    [[PP | 1,0,0,i], [PP | 1,0,0,-i], [PP | 0,1,i,0], [PP | 0,1,-i,0]],
    [[PP | 1,1,1,1], [PP | 1,1,-1,-1], [PP | 1,-1,1,-1], [PP | 1,-1,-1,1]],
    [[PP | 1,1,i,i], [PP | 1,1,-i,-i], [PP | 1,-1,i,-i], [PP | 1,-1,-i,i]],
    [[PP | -1,1,1,1], [PP | 1,-1,1,1], [PP | 1,1,-1,1], [PP | 1,1,1,-1]],
    [[PP | 1,-1,-i,-i], [PP | 1,-1,i,i], [PP | 1,1,-i,i], [PP | 1,1,i,-i]],
    [[PP | 1,i,1,i], [PP | 1,i,-1,-i], [PP | 1,-i,1,-i], [PP | 1,-i,-1,i]],
    [[PP | 1,-i,-i,-1], [PP | 1,-i,i,1], [PP | 1,i,-i,1], [PP | 1,i,i,-1]],
    [[PP | 1,-i,-1,-i], [PP | 1,-i,1,i], [PP | 1,i,-1,i], [PP | 1,i,1,-i]],
    [[PP | 1,i,i,1], [PP | 1,i,-i,-1], [PP | 1,-i,i,-1], [PP | 1,-i,-i,1]]];


///////////////////////
// COMPUTING ISOGENY //
///////////////////////

// Compute the index and scaling for the kernel <R,S> using the 4-torsion lying above
ind, scals := KernelIndex(R,S, RpS, R4, S4, RpS4, O_sq);
"Kernel ", ind; 

P := [X,Y,Z,T];

if ind eq 1 then 
    phi := FourWayMult(Squaring(Hadamard(P)), scals);
else
    phi := FourWayMult(Hadamard(P), scals);
    phi := Eltseq(Matrix([phi])*Transpose(Matrix(AA[ind])));
    phi := Squaring(phi);
end if;

"The (2,2)-isogeny is:";
phi;

////////////////////////
/// CHECKING ISOGENY ///
////////////////////////

P3 := ProjectiveSpace(Fp2, 3);
Kum := Surface(P3, ComputeSquaredKummer(K));

"Checking the isogeny...";
psi := map<Kum -> P3 | phi>;
Kum2<X,Y,Z,T> := Image(psi);
f := DefiningPolynomials(Kum2)[1];
psi := map<Kum -> Kum2 | DefiningPolynomials(psi)>;
OO_sq := Eltseq(psi(O_sq));
new_thetas := [Sqrt(Fp2!o) : o in OO_sq];
K_new := KummerFromThetas(new_thetas);
assert OnSquaredKummer(OO_sq, K_new);
assert Kum2 eq Surface(P3, ComputeSquaredKummer(K_new));

O2 := psi(Kum!R);
kernel := Points((O2 @@ psi));

assert #kernel eq 4;
assert Kum!R in kernel;
assert Kum!S in kernel;
assert Kum!O_sq in kernel;
assert Kum!RpS in kernel;

"Isogeny is correct!";