/*  
    This file constructs the matrices W_ij for an elliptic Kummer surface 
    The matrices are derived from solving_add_matrices.m
*/


if assigned is_main_script then
    filename := "file_loader.m";
    Write(filename, "\n" : Overwrite := true);
else
    is_main_script := true;
    print "add_matrices_squared.m is being executed directly.";
    filename := "file_loader.m";

    files := [
        "../costello-code/Params.m",
        "../costello-code/Kummer.m",
        "../costello-code/Maps.m",
        "../section2/invariants.m",
        "../section2/more_maps.m",
        "../section2/general.m"
        ];
    Write(filename, "\n" : Overwrite := true);
    for file in files do
        tmp :=  "load '" cat file cat "'; \n"; 
        Write(filename, tmp);
    end for;
end if;
load "file_loader.m";
//load "../section2/general.m";

wp := [0,0,1] cat ros;
Zero := K[2];
mu1 := K[2][1];
mu2 := K[2][2];
G := K[1][2];
tau := Fp!Roots(x^2 - G*x + 1)[1][1];

J35 := J_rosenhain![(x - wp[3])*(x - wp[5]), 0];
P35 := RosenhainToKummer(J35, ros, K);
P35 := [P35[i]/P35[4] : i in [1..4]];
P := P35;

// correct choice of tau depends on P[3]
// in practice, we communicate the choice with a bit
if P[3] ne (mu1 - 1/tau)/(mu2 - 1/tau) then
    tau := 1/tau;
end if;

//each Mij cooresponds to the addition by L_ij in K[2]

M12 := Matrix([
    [ 0, 1, 0, 0 ],
    [ 1, 0, 0, 0 ],
    [ 0, 0, 0, 1 ],
    [ 0, 0, 1, 0 ]
]);

M13 := Matrix([
    [ 1, -(mu1 - tau)/(mu2 - tau), tau*(mu1 - tau)/(mu2 - tau), -tau ],
    [ (mu1 - tau)/(mu2 - tau), -1, tau, -tau*(mu1 - tau)/(mu2 - tau) ],
    [ tau*(mu1 - tau)/(mu2 - tau), -tau, 1, -(mu1 - tau)/(mu2 - tau) ],
    [ tau, -tau*(mu1 - tau)/(mu2 - tau), (mu1 - tau)/(mu2 - tau), -1 ]
]);

M14 := Matrix([
    [ 1, -(mu1 - tau)/(mu2 - tau),  1/tau*(mu1 - tau)/(mu2 - tau), -1/tau ],
    [ (mu1 - tau)/(mu2 - tau), -1, 1/tau, -1/tau*(mu1 - tau)/(mu2 - tau) ],
    [  1/tau*(mu1 - tau)/(mu2 - tau), -1/tau, 1, -(mu1 - tau)/(mu2 - tau) ],
    [ 1/tau, -1/tau*(mu1 - tau)/(mu2 - tau), (mu1 - tau)/(mu2 - tau), -1 ]
]);

M15 := Matrix([
    [ 1, -(mu1 - 1/tau)/(mu2 - 1/tau), -1/tau, 1/tau*(mu1 - 1/tau)/(mu2 - 1/tau) ],
    [ (mu1 - 1/tau)/(mu2 - 1/tau), -1, -1/tau*(mu1 - 1/tau)/(mu2 - 1/tau), 1/tau ],
    [ 1/tau, -1/tau*(mu1 - 1/tau)/(mu2 - 1/tau), -1, (mu1 - 1/tau)/(mu2 - 1/tau) ],
    [ 1/tau*(mu1 - 1/tau)/(mu2 - 1/tau), -1/tau, -(mu1 - 1/tau)/(mu2 - 1/tau), 1 ]
]);

M16 := Matrix([
    [ 1, -(mu1 - 1/tau)/(mu2 - 1/tau), -tau, tau*(mu1 - 1/tau)/(mu2 - 1/tau) ],
    [ (mu1 - 1/tau)/(mu2 - 1/tau), -1, -tau*(mu1 - 1/tau)/(mu2 - 1/tau), tau ],
    [ tau, -tau*(mu1 - 1/tau)/(mu2 - 1/tau), -1, (mu1 - 1/tau)/(mu2 - 1/tau) ],
    [ tau*(mu1 - 1/tau)/(mu2 - 1/tau), -tau, -(mu1 - 1/tau)/(mu2 - 1/tau), 1 ]
]);

M23 := Matrix([
    [ 1, -(mu1 - 1/tau)/(mu2 - 1/tau), tau*(mu1 - 1/tau)/(mu2 - 1/tau), -tau ],
    [ (mu1 - 1/tau)/(mu2 - 1/tau), -1, tau, -tau*(mu1 - 1/tau)/(mu2 - 1/tau) ],
    [ tau*(mu1 - 1/tau)/(mu2 - 1/tau), -tau, 1, -(mu1 - 1/tau)/(mu2 - 1/tau) ],
    [ tau, -tau*(mu1 - 1/tau)/(mu2 - 1/tau), (mu1 - 1/tau)/(mu2 - 1/tau), -1 ]
]);

M24 := Matrix([
    [ 1, -(mu1 - 1/tau)/(mu2 - 1/tau), 1/tau*(mu1 - 1/tau)/(mu2 - 1/tau), -1/tau ],
    [ (mu1 - 1/tau)/(mu2 - 1/tau), -1, 1/tau, -1/tau*(mu1 - 1/tau)/(mu2 - 1/tau) ],
    [ 1/tau*(mu1 - 1/tau)/(mu2 - 1/tau), -1/tau, 1, -(mu1 - 1/tau)/(mu2 - 1/tau) ],
    [ 1/tau, -1/tau*(mu1 - 1/tau)/(mu2 - 1/tau), (mu1 - 1/tau)/(mu2 - 1/tau), -1 ]
]);

M25 := Matrix([
    [ 1, -(mu1 - tau)/(mu2 - tau), -1/tau,  1/tau*(mu1 - tau)/(mu2 - tau) ],
    [ (mu1 - tau)/(mu2 - tau), -1, -1/tau*(mu1 - tau)/(mu2 - tau), 1/tau ],
    [ 1/tau, -1/tau*(mu1 - tau)/(mu2 - tau), -1, (mu1 - tau)/(mu2 - tau) ],
    [  1/tau*(mu1 - tau)/(mu2 - tau), -1/tau, -(mu1 - tau)/(mu2 - tau), 1 ]
]);

M26 := Matrix([
    [ 1, -(mu1 - tau)/(mu2 - tau), -tau, tau*(mu1 - tau)/(mu2 - tau) ],
    [ (mu1 - tau)/(mu2 - tau), -1, -tau*(mu1 - tau)/(mu2 - tau), tau ],
    [ tau, -tau*(mu1 - tau)/(mu2 - tau), -1, (mu1 - tau)/(mu2 - tau) ],
    [ tau*(mu1 - tau)/(mu2 - tau), -tau, -(mu1 - tau)/(mu2 - tau), 1 ]
]);

M34 := Matrix([
    [ 0, 0, 0, 1 ],
    [ 0, 0, 1, 0 ],
    [ 0, 1, 0, 0 ],
    [ 1, 0, 0, 0 ]
]);

M35 := Matrix([
    [ 1, 1, -tau, -1/tau ],
    [ 1, 1, -1/tau, -tau ],
    [ tau, 1/tau, -1, -1 ],
    [ 1/tau, tau, -1, -1 ]
]);

M36 := Matrix([
    [ 1,  1/tau^2, -1/tau, -1/tau ],
    [  1/tau^2, 1, -1/tau, -1/tau ],
    [ 1/tau, 1/tau, -1,  -1/tau^2 ],
    [ 1/tau, 1/tau,  -1/tau^2, -1 ]
]);

M45 := Matrix([
    [ 1, tau^2, -tau, -tau ],
    [ tau^2, 1, -tau, -tau ],
    [ tau, tau, -1, -tau^2 ],
    [ tau, tau, -tau^2, -1 ]
]);

M46 := Matrix([
    [ 1, 1, -1/tau, -tau ],
    [ 1, 1, -tau, -1/tau ],
    [ 1/tau, tau, -1, -1 ],
    [ tau, 1/tau, -1, -1 ]
]);

M56 := Matrix([
    [ 0, 0, 1, 0 ],
    [ 0, 0, 0, 1 ],
    [ 1, 0, 0, 0 ],
    [ 0, 1, 0, 0 ]
]);

RingM := Parent(M13);
WW := ZeroMatrix(RingM, 6, 6);
WW[1,2] := M12;
WW[1,3] := M13;
WW[1,4] := M14;
WW[1,5] := M15;
WW[1,6] := M16;
WW[2,3] := M23;
WW[2,4] := M24;
WW[2,5] := M25;
WW[2,6] := M26;
WW[3,4] := M34;
WW[3,5] := M35;
WW[3,6] := M36;
WW[4,5] := M45;
WW[4,6] := M46;
WW[5,6] := M56;

function ApplyWW(i,j,P)
    // Simple function to apply the matrix WW[i,j] = W_ij = Mij to a point P of the Kummer surface
    return Eltseq(WW[i,j]*Transpose(Matrix(Vector(P))));
end function;

// "We can add two torsion points on K_squared :-)";
"add_matrices_squared.m done\n";
