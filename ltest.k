//Linguaggio esercizio 1

module LTEST-SYNTAX
	syntax AExp ::= Int | Id 
					| "read" "(" ")"
					> AExp "/" AExp				[strict]
					| AExp "*" AExp				[strict]
					> AExp "+" AExp				[strict]
					| AExp "-" AExp				[strict] 
					| "(" AExp ")" 				[bracket]		
					
	syntax BExp ::= Bool
					| AExp "<=" AExp			[seqstrict]
					| AExp ">=" AExp			[seqstrict]
					| AExp "<" AExp				[seqstrict]
					| AExp ">" AExp				[seqstrict]
					| AExp "==" AExp			[seqstrict]
					| "(" BExp ")" 				[bracket]	
					
	syntax Block ::= "{" "}"
					| "{" Stmts "}"	
					
	syntax Stmt ::= Block
					| "int" Id "=" AExp ";"						[strict(2)]		//superflua basta int Ids ";" (verificare)
					| "bool" Id "=" BExp ";"					[strict(2)]
					| "int" Ids ";"							
					| Id "=" AExp ";"							[strict(2)]
					| Id "=" BExp ";"							[strict(2)]
					| "if" "(" BExp ")" Block "else" Block		[strict(1)]
					| "while" "(" BExp ")" Block				[strict(1)]
					| "print" "(" AExps ")" ";"					[strict]
					| "(" BExp "?" AExp ":" AExp ";)"			[strict(1)]		
											
	syntax AExps ::= List{AExp,","}				[strict]
	syntax Ids ::= List{Id,","}
	syntax Stmts ::= List{Stmt,""}				[seqstrict]
endmodule

module LTEST
	imports LTEST-SYNTAX
	
	syntax KResult ::= Int | Bool 
			
	configuration <T>
					<k>  $PGM:Stmts </k>		//inizializzo la k cell con il programma passato a krun
					<env> .Map </env>
					<store> .Map </store>					
					<stream>
						<in> .List </in>
						<out> .List </out>
					</stream>
				</T>

	//lookup rule
	rule _:Int => .
	rule .AExps => . 		[structural]
	
	rule <k> X:Id => I:Int ...</k> 
		<env>... X |-> N:Nat ...</env> 
		<store> ... N|-> I ...</store>	  
		
	// read rule
	rule <k> read() => I:Int ...</k>
		<in> ListItem(I) => .List ...</in>	
	// Output
	
	syntax Printable ::= Int | String
	syntax AExp ::= Printable
	rule <k> print(PExp:Printable,ListExp => ListExp); ...</k>
       <out>... .List => ListItem(PExp) </out>  
	rule print(.AExps); => .  						[structural]
	// rule <k> print (I) ; => I ; ...</k>
		// <out>... .List => ListItem(I:Int) </out>
		
	//AExp	  
	rule I1:Int / I2:Int => I1 /Int I2 		when I2 =/=Int 0
	rule I1:Int * I2:Int => I1 *Int I2
	rule I1:Int - I2:Int => I1 -Int I2
	rule I1:Int + I2:Int => I1 +Int I2	  
	
	//BExp
	rule B1:Int <= B2:Int => B1 <=Int B2
	rule B1:Int >= B2:Int => B1 >=Int B2
	rule B1:Int < B2:Int => B1 <Int B2
	rule B1:Int > B2:Int => B1 >Int B2
	rule B1:Int == B2:Int => B1 ==Int B2
	
	//Block
	rule {} => . 		
	// rule <k> {S:Stmt} => S ~> env(Rho:Map) ...</k> <env> Rho </env> [structural]
	rule S1:Stmt S2:Stmt  => S1 ~> S2		[structural]
		
	// rules ripristino ambiente
	// rule env(_) ~> env(Rho) => env(Rho) [structural]
	// quando raggiunge env(Rho) sostiuisce l'attuale ambiente con quello vecchio
	// rule <k> env(Rho) => . ...</k> <env> _ => Rho </env> 	[structural]
		  
	// dichiarazione e assegnamento
	rule <k>int X:Id =I:Int ; => I ...</k>
		<env> Env:Map => Env[N/X] </env>					
		<store> N:Int|-> (_ =>I) </store>		 when notBool (X in keys(Env))
		
	rule <k>bool X:Id =B:Bool ; => B ...</k>
		<env> Env:Map => Env[N/X] </env>					
		<store> N:Int|-> (_ =>B) </store>		 when notBool (X in keys(Env))
		
	//dichiarazione di una lista di identificatori
	rule <k> int (X:Id,Xs:Ids => Xs);...</k>
		<env> Env:Map => Env[N/X]</env>
		<store> N:Int |-> (_ => 0) </store>		when notBool (X in keys(Env))
	
	//if/while stmt
	rule if (true) A else _ => A
	rule if (false) _ else A => A
	rule while (B) A => if (B) {A while (B) A} else {} 		[structural]
	rule ((true) ? S : _ ;) => S
	rule ((false) ? _ : S ;) => S
			
endmodule

