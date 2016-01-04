//Linguaggio esercizio 1

/*@ \section{Introduzione}
Questo è un linguaggio di prova contenente i più basilari costrutti del linguaggio imperativo, 
con le caratteristiche elencate successivamente.

\begin{description}

\item [Assegnamento variabili intere e booleane.] Le variabili assegnate sono registrate nello 'state', 
diviso in 'environment' e 'store', nel primo vengono mappate identificatori a locazioni mentre nel secondo
locazioni a valori.

\item [Creazione costrutti condizionali] Le dichiarazioni condizionali gestiscono due casi semantici,
il caso in cui la condizione venga valutata a true o a false. Nella dichiarazione della sintassi di questi
costrutti appare l'attributo strict(1) in modo da valutare solo il primo argomento (la condizione).

\item [Input e output] Sono permesse operazioni di input e output, rispettivamente con l'espressione read(),
con la quale è possibile leggere un numero intero e valutarlo, e l'espressione print(a1,a2,...,an) la qualev
valuta i suoi argomenti e dopo ritorna i suoi valori.

\end{description}
*/


module LTEST-SYNTAX

/*@ \section{Sintassi}
Con il k-framework in questo modulo viene definita la sintassi utilizzata dal linguaggio usando la notazione
BNF (Backus-Naur Form), con l'espressioni terminali incluse fra apici e le non terminali con lettera maiuscola.
In particolare il k-framework estende la notazione BNF con alcuni attributi e notazioni ispirate al SDF (Syntax 
Definition Formalism) più alcuni elementi specifici di K.
Descrizione di alcuni attributi che vengono usati:
- lefteft;
- strict; indica che tutti gli argomenti verranno valutati (in qualsiasi ordine)
- strict(i); indica che verrà valutato solo l'argomento i-esimo
- seqstrict; indica che gli argomenti verranno valutati in ordine sequenziale (sinistra a destra)
- bracket;
- 

*/
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
	
	/*@ \subsection{The old IMP constructs}
	K distingue una categoria di termini, chiamata KResult, usata per indicare quali termini sono
	da considerare valori o risultati.
	*/		
	syntax KResult ::= Int | Bool 
	 /*Divido lo stato del programma in un 'environment' e uno 'store'
	 l'environment mapperà i nomi delle variabili alle rispettive locazioni,
	 lo store mapperà locazioni ai valori.*/
		
	configuration <T>
					<k>  $PGM:Stmts </k>		//inizializzo la k cell con il programma passato a krun
					<env> .Map </env>
					<store> .Map </store>					
					<stream>
						<in> .List </in>
						<out> .List </out>
					</stream>
				</T>

//@ \subsubsection{Variable lookup}

	rule <k> X:Id => I:Int ...</k> 
		<env>... X |-> N:Nat ...</env> 
		<store> ... N|-> I ...</store>	  
		
	// read rule
	rule <k> read() => I:Int ...</k>
		<in> ListItem(I) => .List ...</in>	
	// Output
	rule <k> print (I) ; => I ; ...</k>
		<out>... .List => ListItem(I:Int) </out>
		
//@ \subsubsection{Arithmetic constructs}
	
	rule I1:Int / I2:Int => I1 /Int I2 		when I2 =/=Int 0
	rule I1:Int * I2:Int => I1 *Int I2
	rule I1:Int - I2:Int => I1 -Int I2
	rule I1:Int + I2:Int => I1 +Int I2	  
	
//@ \subsubsection{Boolean constructs}

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
		  
	// assegnamento  
	rule <k> X:Id =I:Int ; => I; ...</k>
		<env> Env:Map => Env[N/X] </env>					//controllo che la variabile X non sia già nell'ambiente
		<store> N:Int|-> (_ =>I) </store>		 when notBool (X in keys(Env))	//controlla che l'assegnamento del'valore sia dello stesso tipo del valore assegnato
		
	//if/while stmt
	rule if (true) S else _ => S
	rule if (false) _ else S => S
	rule while (B) A => if (B) {A while (B) A} else {} 		[structural]
	rule (true) ? S : _ ; => S
	rule (false) ? _ : S ; => S
			
endmodule

