/*
    The file computees the biqaudratics for the intermediate Kummer surface 
    which is isomorphic to the squared Kummer surface (via the Hadamard map)

    We compute these as the biquadratics on the squared kummer surface are costly
        (see also qDSA by Renes & Smith, url: https://eprint.iacr.org/2017/518) 

    Therefore, we can map points P,Q on K^Sqr to H(P), H(Q) on K^Int, and use the formulas there to compute 
    the difference R. 
    Then H(R) on K^Sqr is the difference of H(P) and H(Q)
*/

// // Uncomment if loading this file by itself:
// load "../costello-code/Kummer.m";

function IntermediateKummer(K)
    //given Squared Kummer K, gives (constants defining) the intermediate kummer surface Kint
    mu := K[2];
    mudual := [m/2 : m in H(mu)]; 
    
    C := 8*mu[1]*mu[2]*mu[3]*mu[4]*mudual[1]*mudual[2]*mudual[3]*mudual[4]/(mudual[1]*mudual[2]-mudual[3]*mudual[4])/(mudual[1]*mudual[3]-mudual[2]*mudual[4])/(mudual[1]*mudual[4]-mudual[2]*mudual[3]);

    return [mu, mudual, [C]];
end function;

function CheckMatrix(PpQ, PmQ)
    // given the two points D = P - Q and S = P + Q 
    // returns the values of the matrix M with M_i,j = S_i*D_j - D_i * S_j
    S := Eltseq(PpQ);
    D := Eltseq(PmQ);

    M := ZeroMatrix(Fp, 4,4);
    for i,j in [1..4] do
        M[i,j] := S[i]*D[j] + D[i]*S[j];
    end for;
    
    return M;
end function;

function BiiValue_int(Kint,i,P,Q)
    // returns the matrices B_{ii} corresponding to the biquadratic forms on the intermediate Kummer surface
    // evaluated in the two points P and Q on this surface. 
    // can be used to verify that R = P \pm Q, or to compute such an R
    // see the optimized Python code for improved efficiency

    // This code is derived from the formulas in qDSA (2017/518)
    // URL: https://eprint.iacr.org/2017/518

    mu := Kint[1];
    mudual := Kint[2];

    mu12 := mu[1]*mu[2];
    mu34 := mu[3]*mu[4];
    eps := [mu[2]*mu34, mu[1]*mu34, mu12*mu[4], mu12*mu[3]];
    kappa := H(eps);

    epsdual := Invert4Constants(mudual);
    Pepsdual := [P[i]^2*epsdual[i] : i in [1..4]];
    Qepsdual := [Q[i]^2*epsdual[i] : i in [1..4]];

    F1 := Pepsdual[1]*Qepsdual[1] + Pepsdual[2]*Qepsdual[2] + Pepsdual[3]*Qepsdual[3] + Pepsdual[4]*Qepsdual[4];
    F2 := Pepsdual[1]*Qepsdual[2] + Pepsdual[2]*Qepsdual[1] + Pepsdual[3]*Qepsdual[4] + Pepsdual[4]*Qepsdual[3];
    F3 := Pepsdual[1]*Qepsdual[3] + Pepsdual[2]*Qepsdual[4] + Pepsdual[3]*Qepsdual[1] + Pepsdual[4]*Qepsdual[2];
    F4 := Pepsdual[1]*Qepsdual[4] + Pepsdual[2]*Qepsdual[3] + Pepsdual[3]*Qepsdual[2] + Pepsdual[4]*Qepsdual[1];
    if i eq 1 then 
        B := mudual[1]*(kappa[1]*F1 + kappa[2]*F2 + kappa[3]*F3 + kappa[4]*F4);
    elif i eq 2 then 
        B := mudual[2]*(kappa[2]*F1 + kappa[1]*F2 + kappa[4]*F3 + kappa[3]*F4);
    elif i eq 3 then 
        B := mudual[3]*(kappa[3]*F1 + kappa[4]*F2 + kappa[1]*F3 + kappa[2]*F4);
    elif i eq 4 then 
        B := mudual[4]*(kappa[4]*F1 + kappa[3]*F2 + kappa[2]*F3 + kappa[1]*F4);
    else 
        "Input index incorrect";
        assert false;
    end if;
    return B;
end function;

function BijValue_int(Kint,i,j,P,Q)
    // returns the matrices B_{ij} corresponding to the biquadratic forms on the intermediate Kummer surface
    // evaluated in the two points P and Q on this surface. 
    // can be used to verify that R = P \pm Q, or to compute such an R
    // see the optimized Python code for improved efficiency

    // This code is derived from the formulas in qDSA (2017/518)
    //  URL: https://eprint.iacr.org/2017/518
    
    mudual := Kint[2];

    k,l := Explode(SetToSequence({1, 2, 3, 4} diff {i,j}));
    
    Cij := mudual[i]*mudual[j]*
            (mudual[i]*mudual[k] - mudual[j]*mudual[l])*
            (mudual[i]*mudual[l] - mudual[j]*mudual[k]);
    
    Pij := P[i]*P[j];
    Pkl := P[k]*P[l];
    Qij := Q[i]*Q[j];
    Qkl := Q[k]*Q[l];
    
    Bij_pre := mudual[k]*mudual[l]*(Pij - Pkl)*(Qij - Qkl)
               + (mudual[i]*mudual[j] - mudual[k]*mudual[l])*(Pkl*Qkl);

    return Kint[3][1]*Cij*Bij_pre;
end function;

function BiiMatrix_int(Kint, P, Q)
    // Given intermediate kummer, finds the Bij

    Fp := Parent(Kint[1][1]);
    BBB := ZeroMatrix(Fp,4,4);
 
    //for point recovery we only need the Bij with 1 <= i < j <= 4

    for i in [1..4] do
        BBB[i,i] := BiiValue_int(Kint, i, P, Q);
    end for;

    for i in [1..3] do
        for j in [i+1..4] do
            BBB[i,j] := BijValue_int(Kint,i,j,P,Q);
            BBB[j,i] := BBB[i,j];
        end for;
    end for;

    return BBB;
end function;

