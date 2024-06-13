// uses Algorithm 5.2 from Robert's paper on biextensions (2024/517)
// to compute pairings on the squared Kummer surface

if assigned is_main_script then
    filename := "file_loader.m";
    Write(filename, "\n" : Overwrite := true);
else
    is_main_script := true;
    print "robert_pairings.m is being executed directly.";
    filename := "file_loader.m";

    files := [
        "../costello-code/Params.m",
        "../costello-code/Kummer.m",
        "../costello-code/Maps.m",
        "../section2/invariants.m",
        "../section2/more_maps.m",
        "../section2/general.m",
        "../section4/biquadratic_general_kummer.m",
        "../section4/biquadratic_intermediate_kummer.m",
        "../section4/point_diff.m",
        "../section3/gaudry_code.m",
        "../section3/fastkummerpairings.m",
        "../section2/add_matrices_squared.m",
        "../section3/v2_and_new_pairings.m"
        ];
    Write(filename, "\n" : Overwrite := true);
    for file in files do
        tmp :=  "load '" cat file cat "'; \n"; 
        Write(filename, tmp);
    end for;
end if;
load "file_loader.m";

//load "../section3/v2_and_new_pairings.m";


J2 := GetAllTwoTorsion(J_rosenhain);
K2 := [ RosenhainToKummer(P, ros, K) : P in J2 ];
//this misses four points, due to bad edge cases for this map
// it misses [1, 0, tau, 0]
// it misses [1, 0, 0, 1/tau]

for i in [1..#K2] do
    if K2[i][1] ne 0 then K2[i] := [Fp!K2[i][j]/K2[i][1] : j in [1..4]]; end if;
end for;

wp := [0, 0, 1] cat ros;
Zero := K[2];
mu1 := K[2][1];
mu2 := K[2][2];
G := K[1][2];
tau := Fp!Roots(x^2 - G*x + 1)[1][1];

////////////////////////////////////////////////////////
//////////////      SIMPLE PAIRINGS       //////////////
////////////////////////////////////////////////////////
total := 10^2;

function RobertPairing(indices, P, K)
    //computes a pairing using the biextensions techniques developed by Robert
    //specifically this implementation is described in the appendix of our paper.

    //////////////////// PRECOMP ////////////////////
    //this first part should all be precomputation
    i, j := Explode(indices);
    if i gt 1 then 
        D_ij := J_rosenhain![(x - wp[i])*(x - wp[j]), 0];
    else //i eq 1 is a shit case...
        k, l, m, n := Explode([ k : k in [1..6] | k ne i and k ne j]);
        D_kl := J_rosenhain![(x - wp[k])*(x - wp[l]), 0];
        D_mn := J_rosenhain![(x - wp[m])*(x - wp[n]), 0];
        D_ij := D_kl + D_mn;
    end if;
    
    L_ij := RosenhainToKummer(D_ij, ros, K);

    //we take the first nonzero as the normalizing index for the monodromy computation
    normalizing_index := [i : i in [1..4] | P[i] ne 0 and L_ij[i] ne 0][1];
    ni := normalizing_index;
    L_ij := [L_ij[i]/L_ij[ni] : i in [1..4]];

    ML := ApplyWW(i,j, L_ij);
    lambda1 := ML[ni]/Zero[ni];
    assert [Zero[i]*lambda1 : i in [1..4]] eq ML;
    //everything up to here was precomputation
    //////////////////// PRECOMP ////////////////////
    
    //normalize P to normalizing index
    P := [P[i]/P[ni] : i in [1..4]];
    D := PointDifferenceSquared(P, L_ij, K);
    D := [D[i]/D[ni] : i in [1..4]];
    MD := ApplyWW(i,j, D);
    lambda2 := MD[ni]/P[ni]; 
    assert MD eq [P[i]*lambda2 : i in [1..4]];

    T_zeta := lambda2/lambda1;
    return Fp!T_zeta;
end function;


Indices := [<i,j> : i,j in [1..6] | i lt j];

worked := [ <i,0> : i in Indices];


//here we test if the two ways we compute pairings (using Roberts approach and our own)
//match up. If the score is 50%, it means we failed. If it is 0 or 100%, it is correct
//but there might be a slight mismatch in sign. 

for i in [1..total] do
    Q := RandomKummerPoint(K);
    v02_result := [ IsSquare(Fp!NewPairing(indices, Q, K)) : indices in Indices ];
    robert_result := [IsSquare(Fp!RobertPairing(indices, Q, K)) : indices in Indices];
    for j in [1..#Indices] do
        if v02_result[j] eq robert_result[j] then worked[j][2] +:= 1; end if;
    end for;
end for;

"WARNING: due to the choice of tau <--> 1/tau, the scores below might be 0% instead of 100%";
"In practice, this does not matter, and can be resolved by fixing a choice.";

for scores in worked do
    printf "for %o: Roberts equal to classical: %o%%\n", scores[1], Round(100*scores[2]/total*1.0);
end for;

assert {scores[2] : scores in worked} eq {100} or {scores[2] : scores in worked} eq {0, 100} ;


"Robert Pairing using monodromies WORKS";
"robert_pairings.m done\n";

////////////////////////////////////////////////////////
////////////   OLD TEDIOUS MANUAL STUFF   //////////////
////////////////////////////////////////////////////////

//below is how I did everything first, by hand, working
//out the notes from Robert, which I in the end summarized
//in the single function you see above.

//so this is just left here for bug-fixing or so


// // the point P = [d : c : b : a]
// i := 3; j := 4; 
// J34 := J_rosenhain![(x - wp[i])*(x - wp[j]), 0];
// P34 := RosenhainToKummer(J34, ros, K);
// P34 := [P34[i]/P34[1] : i in [1..4]];

// // the point P = [c : d : a : b]
// i := 5; j := 6; 
// J56 := J_rosenhain![(x - wp[i])*(x - wp[j]), 0];
// P56 := RosenhainToKummer(J56, ros, K);
// P56 := [P56[i]/P56[1] : i in [1..4]];

// // the point P = [b : a : d : c]
// J12 := J34 + J56;
// P12 := RosenhainToKummer(J12, ros, K);
// P12 := [P12[i]/P12[1] : i in [1..4]];



// printf "\nworking with the pairing for (1,2)\n";
// //this is hardcoded what translation by the above point P means
// function TranslationByP12(Q) 
//     return [Q[2], Q[1], Q[4], Q[3]]; 
// end function;

// assert TranslationByP12(Zero) eq normalise(P12);
// assert normalise(TranslationByP12(P12)) eq Zero;

// //algorithm 5.2 by Roberts (private communcation)
// MP12 := TranslationByP12(P12);
// lambda12 := MP12[1]/Zero[1];
// assert [Zero[i]*lambda12 : i in [1..4]] eq MP12;

// worked := 0;

// function Robert12(Q)
//     //algorithm 5.2 by Roberts (private communcation)
//     Q := normalise(Q);
//     D := normalise(PointDifferenceSquared(Q, P12, K));
//     MD := TranslationByP12(D); 
//     lambda := MD[1]/Q[1]; 
//     assert MD eq [Q[i]*lambda : i in [1..4]];

//     T_zeta := lambda/lambda12;
//     T := IsSquare(Fp!T_zeta);
//     return T;
// end function;

// for i in [1..total] do
//     Q := RandomKummerPoint(K);
//     rtp_theta := IsSquare(Fp!NewPairing(<1,2>, Q, K));
//     if Robert12(Q) eq rtp_theta then worked +:= 1; end if;
// end for;

// printf "Roberts was equal to classical: %o%%\n", Round(100*worked/total*1.0);

// ////////////////////////////////////////////////////////

// printf "\nworking with the pairing for (3,4)\n";
// //this is hardcoded what translation by the above point P means
// function TranslationByP34(Q) 
//     return [Q[4], Q[3], Q[2], Q[1]]; 
// end function;

// assert normalise(TranslationByP34(Zero)) eq normalise(P34);
// assert normalise(TranslationByP34(P34)) eq Zero;

// //algorithm 5.2 by Roberts (private communcation)
// MP34 := TranslationByP34(P34);
// lambda34 := MP34[1]/Zero[1];
// assert [Zero[i]*lambda34 : i in [1..4]] eq MP34;

// worked := 0;

// function Robert34(Q)
//     //algorithm 5.2 by Roberts (private communcation)
//     Q := normalise(Q);
//     D := normalise(PointDifferenceSquared(Q, P34, K));
//     MD := TranslationByP34(D); 
//     lambda := MD[1]/Q[1]; 
//     assert MD eq [Q[i]*lambda : i in [1..4]];

//     T_zeta := lambda/lambda34;
//     T := IsSquare(Fp!T_zeta);
//     return T;
// end function;

// for i in [1..total] do
//     Q := RandomKummerPoint(K);
//     rtp_theta := IsSquare(Fp!NewPairing(<3,4>, Q, K));
//     if Robert34(Q) eq rtp_theta then worked +:= 1; end if;
// end for;

// printf "Roberts was equal to classical: %o%%\n", Round(100*worked/total*1.0);

// ////////////////////////////////////////////////////////

// printf "\nworking with the pairing for (5,6)\n";
// //this is hardcoded what translation by the above point P means
// function TranslationByP56(Q) 
//     return [Q[3], Q[4], Q[1], Q[2]]; 
// end function;

// assert normalise(TranslationByP56(Zero)) eq normalise(P56);
// assert normalise(TranslationByP56(P56)) eq Zero;

// //algorithm 5.2 by Roberts (private communcation)
// MP56 := TranslationByP56(P56);
// lambda56 := MP56[1]/Zero[1];
// assert [Zero[i]*lambda56 : i in [1..4]] eq MP56;

// worked := 0;

// function Robert56(Q)
//     //algorithm 5.2 by Roberts (private communcation)
//     Q := normalise(Q);
//     D := normalise(PointDifferenceSquared(Q, P56, K));
//     MD := TranslationByP56(D); 
//     lambda := MD[1]/Q[1]; 
//     assert MD eq [Q[i]*lambda : i in [1..4]];

//     T_zeta := lambda/lambda56;
//     T := IsSquare(Fp!T_zeta);
//     return T;
// end function;

// for i in [1..total] do
//     Q := RandomKummerPoint(K);
//     rtp_theta := IsSquare(Fp!NewPairing(<5,6>, Q, K));
//     if Robert56(Q) eq rtp_theta then worked +:= 1; end if;
// end for;

// printf "Roberts was equal to classical: %o%%\n", Round(100*worked/total*1.0);

// ////////////////////////////////////////////////////////


// i := 3; j := 5; 
// J35 := J_rosenhain![(x - wp[i])*(x - wp[j]), 0];
// P35 := RosenhainToKummer(J35, ros, K);
// P35 := [P35[i]/P35[4] : i in [1..4]];
// P := P35;

// //correct choice of tau
// if P[3] ne (mu1 - 1/tau)/(mu2 - 1/tau) then
//     tau := 1/tau;
// end if;

// printf "\nworking with the pairing for (3,5)\n";

// M_P := Matrix([
//     [-1, -1, tau, 1/tau],
//     [-1, -1, 1/tau, tau],
//     [-tau, -1/tau, 1, 1],
//     [-1/tau, -tau, 1, 1]
// ]);


// //this was computed tediously using solving_robert.m
// function TranslationByP(Q) 
//     return Eltseq(M_P*Transpose(Matrix(Vector(Q)))); 
// end function;

// assert normalise(TranslationByP(Zero)) eq normalise(P);
// assert normalise(TranslationByP(P)) eq Zero;


// //testing M_P
// D_test := [ Random(J_rosenhain) : i in [1..100]];
// D_test := [ <D, D + J35> : D in D_test];
// K_test := [ <RosenhainToKummer(D[1], ros, K), RosenhainToKummer(D[2], ros, K)> : D in D_test];

// for Q in K_test do assert normalise(TranslationByP(Q[1])) eq normalise(Q[2]); end for;
// printf "addition by (3,5) matrix verified\n";

// //algorithm 5.2 by Roberts (private communcation)
// //fails for these particular, non-symmetric, points
// //first approach
// MP := TranslationByP(P);
// lambda1 := MP[4]/Zero[4];
// assert [Zero[i]*lambda1 : i in [1..4]] eq MP;

// worked := 0;

// for i in [1..total] do

//     //algorithm 5.2 by Roberts (private communcation)
//     Q := normalise(RandomKummerPoint(K));
//     D, S := PointDifferenceSquaredBoth(Q, P, K);
//     D := normalise(D); S := normalise(S);
//     MD := TranslationByP(D); 
//     lambda2 := MD[4]/Q[4]; 
//     assert MD eq [Q[i]*lambda2 : i in [1..4]];

//     T_zeta := lambda2/lambda1;
//     T := IsSquare(Fp!T_zeta);

//     MS := TranslationByP(S); 
//     lambda3 := MS[4]/Q[4]; 
//     assert MS eq [Q[i]*lambda3 : i in [1..4]];

//     T_zeta2 := lambda3/lambda1;
//     T2 := IsSquare(Fp!T_zeta2);

//     //old method
//     zeta := FastTwoPairing(<3,5>, Q, K);
//     rtp_theta := IsSquare(Fp!zeta);

//     //new method
//     zeta2 := NewPairing(<3,5>, Q, K);
//     rtp_theta2 := IsSquare(Fp!zeta2);

//     //assert rtp_theta eq rtp_theta2;

//     // printf "Classical results: %o\n", <rtp_theta, zeta>;
//     // printf "Roberts   results: %o\n\n", <T, T_zeta>;
//     if T eq rtp_theta2 then worked +:= 1; end if;
// end for;

// printf "Roberts was equal to classical: %o%%\n", Round(100*worked/total*1.0);
