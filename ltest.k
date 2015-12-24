//Linguaggio esercizio 1

module LTEST-SYNTAX
	syntax Exp1 ::= Int | Id
					| "read" "(" ")"
					> Exp1 "/" Exp1				[left,strict]
					| Exp1 "*" Exp1				[left,strict]
					> Exp1 "+" Exp1				[left,strict]
					| Exp1 "-" Exp1				[left,strict] 
					| "(" Exp1 ")" 				[bracket]		
					
	syntax Exp2 ::= Bool
					| Exp1 "<=" Exp1			[seqstrict]
					| Exp1 ">=" Exp1			[seqstrict]
					| Exp1 "<" Exp1				[seqstrict]
					| Exp1 ">" Exp1				[seqstrict]
					| Exp1 "==" Exp1			[seqstrict]
					| "(" Exp2 ")" 				[bracket]	
					
	syntax Block ::= "{" "}"
					| "{" Stmts "}"	
					
	syntax Stmt ::= Block
					| Exp1 ";"
					| "if" "(" Exp2 ")" Block "else" Block		[strict(1)]
					| "while" "(" Exp2 ")" Block			[strict(1)]
					| "print" "(" Exp1 ")" ";"			[strict]
					| Exp2 "?" Exp1 ":" Exp1			[strict(1)]		
					| Id "=" Exp1 ";"				[strict(2)]
					| Id "=" Exp2 ";"				[strict(2)]

	syntax Exp1s ::= List{Exp1,","}				[strict]
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
	rule <k> read() => I:Int </k>
		<in> ListItem(I) => .List ...</in>	
	// Output
	// rule <k> print I:Exp1 ; => . </k>
		// <out> . => ListItem(I) </out>
		
	//Exp1	  
	rule I1:Int / I2:Int => I1 /Int I2 		when I2 =/=Int 0
	rule I1:Int * I2:Int => I1 *Int I2
	rule I1:Int - I2:Int => I1 -Int I2
	rule I1:Int + I2:Int => I1 +Int I2	  
	
	//Exp2
	rule B1:Int <= B2:Int => B1 <=Int B2
	rule B1:Int >= B2:Int => B1 >=Int B2
	rule B1:Int < B2:Int => B1 <Int B2
	rule B1:Int > B2:Int => B1 >Int B2
	rule B1:Int == B2:Int => B1 ==Int B2
	
	//Block
	rule {} => . 				
	rule <k> {S:Stms} => S ~> env(Rho:Map) ...</k> <env> Rho </env> [structural]
	rule S1:Stmt S2:Stmt => S1 ~> S2
		
	// rules ripristino ambiente
	rule env(_) ~> env(Rho) => env(Rho) [structural]
	 // quando raggiunge env(Rho) sostiuisce l'attuale ambiente con quello vecchio
	rule <k> env(Rho) => . ...</k> <env> _ => Rho </env> 	[structural]
		  
	// assegnamento  
	rule <k> X:Id =I:Int ; => I ...</k>
		<env> Env:map => Env[N/X]</env>			when notBool (X in keys(Env))		//controllo che la variabile X non sia già nell'ambiente
		<store>... N:Int |-> (_ =>I) ...</store>		 	//controlla che l'assegnamento del'valore sia dello stesso tipo del valore assegnato
		
	//if/while stmt
	rule if (true) A else _ => A
	rule if (false) _ else A => A
	rule while (B) A => if (B) {A while (B) A} else {} 		[structural]
			
endmodule

