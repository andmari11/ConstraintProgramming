include "alldifferent.mzn";
% domino table 8x7
array[1..8,1..7] of var 1..28: domino; %There are 28 tiles
array[1..8,1..7] of var 0..3: solution;
%0 arriba
%1 abajo
%2 izquierda
%3 derecha

%every number appears in the table (only once)
%constraint forall (e in 1..28) (exists (i in 1..8, j in 1..7) (domino[i,j]=e));
constraint forall (e in 1..28) ((sum (i in 1..8, j in 1..7) (domino[i,j]=e)) = 2);

% vertical relation 
constraint forall (i in 2..8, j in 1..7 ) ((solution[i,j] = 0) -> (domino[i-1,j]= domino[i,j]));

% hrizontal relation 
constraint forall (i in 1..8, j in 2..7 ) ((solution[i,j] = 2) -> (domino[i,j-1]= domino[i,j]));


%%%And now we just need that it has solution
% condition on first row
constraint forall (i in 1..7 ) (solution[1,i] != 0);

% condition on last row
constraint forall (i in 1..7 ) (solution[8,i] != 1);

% condition on first column
constraint forall (i in 1..8 ) (solution[i,1] != 2);

% condition on last column
constraint forall (i in 1..8 ) (solution[i,7] != 3);


% vertical consistency condition
constraint forall (i in 2..8, j in 1..7 ) ((solution[i,j] = 0) = (solution[i-1,j]= 1));

% horizontal consistency condition
constraint forall (i in 1..8, j in 2..7 ) ((solution[i,j] = 2) = (solution[i,j-1]= 3));

%exists an horizontal in 5..8x5..7 <--needed
%constraint exists (i in 5..8, j in 5..7) (solution[i,j]> 1);

%Not all vertical every two rows <-- needed
%constraint forall (r in 1..4) (exists (i in 2*r-1..2*r, j in 1..7) (solution[i,j]> 1)); 

% Fix some position
%constraint domino[3,4] = 14;

solve satisfy;

output [ "Board: \n" ];

output [ "\(domino[i,j])" ++ 
         if j == 7 then "\n" else " " endif |
         i in 1..8, j in 1..7
];

output [ "Solution: \n" ];

output [ "\(solution[i,j])" ++ 
         if j == 7 then "\n" else " " endif |
         i in 1..8, j in 1..7
];
