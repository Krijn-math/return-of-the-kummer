/*
    This gives a symbolic proof of the Lemma on the twist of Kummers.
    
    Given a set b0, b1, g0, g1 of an elliptc kummer K_alpha, it generates the 
    Rosenhain invariants for both K_alpha and its twist and verifies they are correct.
    
    The map Kappa derived by Costello (2018/850) differs given alpha and -alpha
    and this file shows that the e's defined by these two different maps differ by a non-square.
    Hence, only one of the two maps kappa's is defined over Fp, the other has imaginairy y-part.
*/

if assigned is_main_script then
    filename := "file_loader.m";
    Write(filename, "\n" : Overwrite := true);
else
    is_main_script := true;
    print "TwistProof.m is being executed directly.";
    filename := "file_loader.m";

    files := [
        "../costello-code/Params.m",
        "../costello-code/Kummer.m",
        "../costello-code/Maps.m",
        "../section2/invariants.m",
        "../section2/more_maps.m"
        ];
    Write(filename, "\n" : Overwrite := true);
    for file in files do
        tmp :=  "load '" cat file cat "'; \n"; 
        Write(filename, tmp);
    end for;
end if;
load "file_loader.m";
//load "../section2/invariants.m";
//load "../section2/more_maps.m";


Ff<b0, b1, g0, g1> := FunctionField(Fp, 4);

function Invar(b0, b1, g0, g1)
 	lambda := -(b0*g1+b1*g0)*(b0*g0+b1*g1)/((b0*g0-b1*g1)*(b0*g1-b1*g0));
    mu := (b0*g0 + b1*g1)*(b0*g0 - b1*g1)/((b0*g1 + b1*g0)*(b0*g1 - b1*g0));
    nu := - (b0*g0 + b1*g1)^2/(b0*g1 - b1*g0)^2;
    return lambda, mu, nu;
end function;

//for -alpha, these are the b0, b1, g0, g1 values
twb0 := -b1; twb1 := b0;
twg0 := -g1; twg1 := g0;

lambda, mu, nu := Invar(b0, b1, g0, g1);
twlambda, twmu, twnu := Invar(twb0, twb1, twg0, twg1);
assert lambda eq twlambda;
assert mu eq twmu;
assert nu eq twnu;
assert nu eq lambda*mu;
print "twisting ell curves is twisting kummers";


function ZsAndABCDE(b0, b1, g0, g1)
    //this function computes the roots, and then from the roots computes the 
    //values a, b, c, d, e2 used in the Kappa map C_alpha --> C_rosenhain

    lambda, mu, nu := Invar(b0, b1, g0, g1);

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
    return [z1, z2, z3, z4, z5, z6], [a, b, c, d, e2];
end function;

//we compute the Kappa values for both the original and the twist of the curve
Zs, ABCDE := ZsAndABCDE(b0, b1, g0, g1);
twZs, twABCDE := ZsAndABCDE(twb0, twb1, twg0, twg1);
e2 := ABCDE[5];
twe2 := twABCDE[5];

//this verifies they differ by a non-square
differ := e2/twe2;
if IsSquare(differ) eq false then
    print "e2 and its twist differ by nonsquare";
end if;


//now lets show that this actually works

E := E_alpha;
P := Random(E_alpha);
twP := [-P[1], i*P[2]];
twE := KernelPointToMont(twP);
twP := twE!twP;

K, KP, C, J, Jr, kappa, EtaP := AlphaAndPointToKummerUnderTheHood(alpha, P);
twK, twKP, twC, twJ, twJr, twkappa, twEtaP := AlphaAndPointToKummerUnderTheHood(-alpha, twP);

assert TwistKummer(K)eq twK;

twKP2 := TwistPoint(KP);
assert OnKummer(twKP2, twK);

