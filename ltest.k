//Linguaggio esercizio 1

module LTEST-SYNTAX
	syntax AExp ::= Int | Id
					| "read" "(" ")"
					> AExp "/" AExp				[left,strict]
					| AExp "*" AExp				[left,strict]
					> AExp "+" AExp				[left,strict]
					| AExp "-" AExp				[left,strict] 
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
					| AExp ";"
					| "if" "(" BExp ")" Block "else" Block		[strict(1)]
					| "while" "(" BExp ")" Block			[strict(1)]
					| "print" "(" AExp ")" ";"			[strict]
					| BExp "?" AExp ":" AExp			[strict(1)]		
					| Id "=" AExp ";"				[strict(2)]
					| Id "=" BExp ";"				[strict(2)]

	syntax AExps ::= List{AExp,","}				[strict]
	syntax Stmts ::= List{Stmt,""}				[seqstrict]
endmodule

module LTEST
	imports LTEST-SYNTAX
	
	syntax KResult ::= Int | Bool 
	// Divido lo stato del programma in un 'environment' e uno 'store'
	// l'environment mapperà i nomi delle variabili alle rispettive locazioni,
	// lo store mapperà locazioni ai valori.
		
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
	rule <k> X:Id => I:Int ...</k> 
		<env>... X |-> N:Nat ...</env> 
		<store> ... N|-> I ...</store>	  
		
	// read rule
	rule <k> read() => I:Int ...</k>
		<in> ListItem(I) => .List ...</in>	
	// Output
	// rule <k> print I:Stmts => .  ...</k>
		// <out>... . => ListItem(I) ...</out>
		
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
	rule <k> {S} => S ~> env(Rho) ...</k> <env> Rho </env> [structural]
	rule S1:Stmt S2:Stmt => S1 ~> S2
		
	// rules ripristino ambiente
	rule env(_) ~> env(Rho) => env(Rho) [structural]
	 // quando raggiunge env(Rho) sostiuisce l'attuale ambiente con quello vecchio
	rule <k> env(Rho) => . ...</k> <env> _ => Rho </env> 	[structural]
		  
	// assegnamento  
	rule <k> X =I:Int => I ...</k>
		<env>... X|-> N ...</env>			when notBool (X in keys(Env))		//controllo che la variabile X non sia già nell'ambiente
		<store>... N|-> (_ =>I) ...</store>		 	//controlla che l'assegnamento del'valore sia dello stesso tipo del valore assegnato
		
	//if/while stmt
	rule if (true) A else _ => A
	rule if (false) _ else A => A
	rule while (B) A => if (B) {A while (B) A} else {} 		[structural]
			
endmodule

