% simple clustering problem

include "globals.mzn";

int: n; % number of data points
set of int: POINTS = 1..n;

int: k; % at most k clusters
set of int: CLUSTERS = 1..k;

int: l; % lower bound on the number of distinct clusters
constraint assert(l <= k, "Lower bound must be lteq k");
var l..k: distinctClusters; 

bool: forceAtLeastOne; 

float: maxdiam;

array[POINTS, POINTS] of float: costs;
int: maxCost = round(max( [costs[i,j] | i, j in POINTS]));

array[POINTS] of var CLUSTERS: map; % now there's a bunch of symmetry, so I want to restrict valid assignments 

% put bounds on the number of clusters
constraint nvalue(distinctClusters, map);

% symmetry constraints to tie down all instances to one representative of the equivalence class
%constraint forall(i in 1..n - 1) (
%  min( [ j | j in POINTS where map[j] = i ]  ) < min([j | j in POINTS where map[j] = i+1]) 
%);

% more compactly as global constraint: i < j implies that i appears at least once before j in map 
constraint value_precede_chain([i | i in 1..k], map);

constraint forall(i, j in POINTS where i < j /\ map[i] = map[j]) (
  costs[i,j] <= maxdiam
);

constraint if forceAtLeastOne then 
  global_cardinality_low_up_closed(map, [i | i in 1..k], 
                                        [ 1 | i in 1..k ], [n-k+1 | i in 1.. k]) 
else true endif;

var int: objective = min(i, j in POINTS where i < j) (
  if map[i] != map[j] then round(costs[i,j]) else maxCost+1 endif
); 

solve minimize objective;

output[ show(map[i]) ++ if i = n then "" else ", " endif | i in POINTS ];