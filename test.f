x:Bool;

x;

f:Bool->Bool;

f true;

(lambda y:Bool.y) x;

 lambda x:Bool. x;
 
 (lambda x:Bool->Bool. if x false then true else false) 
   (lambda x:Bool. if x then false else true); 

(lambda x:Bool->Bool.x true) (lambda x:Bool. if x then false else true);