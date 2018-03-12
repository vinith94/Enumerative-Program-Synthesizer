#include <SynthLib2ParserIFace.hpp>
#include <iostream>
#include <string>
#include <sstream>
#include <vector>
#include <algorithm>
#include <stdint.h>
#include "z3++.h"
#include "fstream"
#include "exprtk.hpp"

using namespace std;
using namespace SynthLib2Parser;

vector<string> matchAndAction(vector<string> I, vector<string> E, string M)
{
  string tmp = "";
  vector<string> R;
  R.clear();
  
  for(uint32_t i=0; i < I.size(); i++)
  {
      for(uint32_t j=0; j < E.size(); j++)
      {
          tmp = I[i];
          I[i].replace(I[i].find(M),M.length(),E[j]);
          R.push_back(I[i]);
          I[i] = tmp;
      }
  }

  return R;
}

int numOfOcuurancesOfSubStrInStr (string str, string substr)
{
    int count = 0;
    size_t nPos = str.find(substr, 0);
    while(nPos != string::npos)
    {
        count++;
        nPos = str.find(substr, nPos+1);
    }

    return count;
}

vector<string> enumerateExpForSingleProduction( string production, vector<string> nonTerminalInfo, vector< vector<string> > itemsToBeReplacedWithNonTerminal)
{
  vector<string> result;
  result.clear();

  result.push_back(production);

  for(uint32_t i = 0; i < nonTerminalInfo.size(); i++)
  {
      int count = numOfOcuurancesOfSubStrInStr( production , nonTerminalInfo[i]);
       
      while(count)
      {
          result = matchAndAction(result, itemsToBeReplacedWithNonTerminal[i], nonTerminalInfo[i]);
          count --;
      }
       
  }

  return result;
}

int findPositionOfElementInVector( vector<string> inputVector, string searchElement)
{
  vector<string>::iterator it;

  it = find (inputVector.begin(), inputVector.end(), searchElement);

  if (it != inputVector.end())
    return (distance(inputVector.begin(), it));
  else
    std::cout << "Element not found in inputVector\n";

  return -1;
}

vector<string> enumerateExpForAllProduction(vector<string> E, vector<string> nonTerminalInfo, vector< vector<string> > priortyOrderProductions)
{
  vector< vector<string> > itemsToBeReplacedWithNonTerminal;
  itemsToBeReplacedWithNonTerminal.clear();
 
  for(uint32_t i = 0; i < nonTerminalInfo.size(); i++)
  {
      if(i == 0)
      {
            itemsToBeReplacedWithNonTerminal.push_back(E);
      }
      else
      {
            itemsToBeReplacedWithNonTerminal.push_back(vector<string>());
      }
  }

  vector<string> C; //Result: All enumerated expressions for given Prog Size using E and G
  vector<string> R; //Temp Vector
  C.clear(); 
  int pos;

  for(uint32_t i = 0; i < priortyOrderProductions.size(); i++)
  {
          R.clear();

	  R = enumerateExpForSingleProduction(priortyOrderProductions[i][1], nonTerminalInfo, itemsToBeReplacedWithNonTerminal);

	  if(priortyOrderProductions[i][0] == nonTerminalInfo[0])
	  {
		  C.insert(C.end(), R.begin(), R.end());
	  }
	  else
	  {
		  pos = findPositionOfElementInVector(nonTerminalInfo, priortyOrderProductions[i][0]);
		  (itemsToBeReplacedWithNonTerminal[pos]).insert((itemsToBeReplacedWithNonTerminal[pos]).end(), R.begin(), R.end());
	  }
  }

  return C;

}

bool doesExprSatisfiesPoints(string expr)
{
/*   typedef exprtk::expression<double> expression_t;
    typedef exprtk::parser<double> parser_t;

    string expression_string = "(2 + 3)";

    expression_t expression;

    parser_t parser;

    if (parser.compile(expression_string,expression))
    {
      double result = expression.value();

      cout << "Result is "<< result << endl;

      exit(0);
    }
*/
    return true;
}

bool checkExprAgainstSpec(string expression)
{
    using namespace z3;

    z3::context c;

    Z3_ast asty;
    asty = Z3_parse_smtlib2_string(c,expression.c_str() , 0, 0, 0, 0, 0, 0);

    expr ex(c,asty);
    solver s(c);

    s.add(!ex);

    if(s.check() == sat ) 
    {
      //cout << s.get_model() << endl;

      model m = s.get_model();

      ofstream file;
      file.open("model.txt");
      file << m << "\n";
      file.close();
      //exit(0);

      return false;
    }
    else
    {
      //cout << "Proved" << endl;
      //exit(0);
      return true;
    }
}

bool checkEquivalance(string expr)
{
    return false;
}

int main(int argc, char* argv[])
{

  SynthLib2Parser::SynthLib2Parser* Parser = new SynthLib2Parser::SynthLib2Parser();
  try {
      (*Parser)(argv[1]);
  } catch (const exception& Ex) {
      cout << Ex.what() << endl;
      exit(1);
  }

  SynthFunCmd* synthFun;
  NTDef* ntDef;
  GTerm* gT;
  SymbolGTerm* symGT;
  FunGTerm* funGT;
  Literal* lit;

  string ntName;
  string prodFunName;
  string prodFunArgName;

  stringstream prod;
  stringstream constraintStream;
  stringstream assertStream;
  stringstream variableStream;
  stringstream varStream;
  stringstream funStream;
  stringstream funSort;
  string funName;

  vector<string> E;
  E.clear();

  vector<string> nonTerminalInfo;
  nonTerminalInfo.clear();

  vector<string> temp;
  temp.clear();

  vector< vector<string> > priortyOrderProductions;
  priortyOrderProductions.clear();

  vector<string> argVar;
  vector< vector<int> > points;
  vector< vector<int> > tmpPoints;
  stringstream argSort;

  for(auto const& Cmd : (Parser->GetProgram())->GetCmds())
  {
          switch(Cmd->GetKind())
	  {

		  case CMD_SYNTHFUN  :
			  {
				  synthFun =  static_cast<SynthFunCmd*>(Cmd);

                                  funName = synthFun->GetFunName();

                                  funSort << *synthFun->GetSort();

                                  for(auto const& ASPair : synthFun->GetArgs())
                                  {
                                         argVar.push_back(ASPair->GetName());
                                         points.push_back(vector<int>());
                                         tmpPoints.push_back(vector<int>());
                                         argSort.str(""); argSort.clear();
                                         argSort << *ASPair->GetSort();
                                         if(argSort.str() != "Int")
                                         {
                                              exit(0);
                                         }
                                         //cout << argVar.back() <<*ASPair->GetSort() << endl;
                                  }

				  for(uint32_t i = 0; i < synthFun->GetGrammarRules().size(); i++)
                                  {
                                            ntDef = (synthFun->GetGrammarRules()[i]);

                                            ntName =  ntDef->GetName();
                                            ntName.push_back('}');
                                            ntName.insert(0,1,'{');

                                            if(find(nonTerminalInfo.begin(), nonTerminalInfo.end(), ntName) == nonTerminalInfo.end())
                                            {
                                                  nonTerminalInfo.push_back(ntName);
                                            }

                                            //cout << ntName << endl;

                                            for(uint32_t j = 0; j < ntDef->GetExpansions().size(); j++)
                                            {
                                                 gT = (ntDef->GetExpansions()[j]);

                                                 //cout << gT->GetKind() << endl;

                                                 switch(gT->GetKind())
                                                 {
                                                      case GTERMKIND_SYMBOL:
                                                           {
                                                               symGT = static_cast<SymbolGTerm*>(gT);

                                                               //cout << symGT->GetSymbol() << endl;

                                                               E.push_back(symGT->GetSymbol());

                                                               break;
                                                           }
                                                      case GTERMKIND_FUN:
                                                           {
                                                               funGT = static_cast<FunGTerm*>(gT);

                                                               temp.push_back(ntName);

                                                               //cout << funGT->GetName() << endl;

                                                               prodFunName = funGT->GetName();

                                                               prod << "(" << prodFunName;

                                                               for(uint32_t k = 0; k < funGT->GetArgs().size(); k++)
                                                               {
                                                                    //cout << (funGT->GetArgs()[k])->GetKind() << endl;

                                                                    switch((funGT->GetArgs()[k])->GetKind())
                                                                    {
                                                                       case GTERMKIND_SYMBOL:
                                                                            {
                                                                                 symGT = static_cast<SymbolGTerm*>(funGT->GetArgs()[k]);

                                                                                 //cout << symGT->GetSymbol() << endl;

                                                                                 prodFunArgName = symGT->GetSymbol();

                                                                                 // How to add only if this symbol is NT ??
                                                                                 prodFunArgName.push_back('}');
                                                                                 prodFunArgName.insert(0,1,'{');

                                                                                 //cout << prodFunArgName << endl;
                                                                                 break;
                                                                            }
                                                                       default:
                                                                            {
                                                                                 exit(0);
                                                                            }
                                                                    }

                                                                    prod << " " << prodFunArgName;
                                                               }

                                                               prod << ")";

                                                               temp.push_back(prod.str());
                                                               priortyOrderProductions.push_back(temp);
                                                               temp.clear();

                                                               //cout << prod.str() << endl;

                                                               prod.str("");

                                                               break;
                                                           }
                                                      case GTERMKIND_LITERAL:
                                                           {
                                                               lit = (static_cast<LiteralGTerm*>(gT))->GetLiteral();

                                                               //cout << lit->GetLiteralString() << endl;

                                                               E.push_back(lit->GetLiteralString());

                                                               break;
                                                           }
                                                      default:
                                                           {
                                                               exit(0);
                                                           }
                                                 }
                                            }
                                  }

				  break;
			  }
                  case CMD_VARDECL:
                          {
                                  VarDeclCmd* variableDecl =  static_cast<VarDeclCmd*>(Cmd);

                                  variableStream <<"(declare-fun "<<variableDecl->GetName() <<" ( ) "<< *variableDecl->GetSort()<<" )\n";

                                  varStream << "(" << variableDecl->GetName() << " " << *variableDecl->GetSort() << ") ";

                                  //cout << variableStream.str();

                                  break;
                          }
                  case CMD_CONSTRAINT:
                          {
                                  ConstraintCmd* constraint =  static_cast<ConstraintCmd*>(Cmd);

                                  constraintStream << (*constraint->GetTerm()) << " ";

                                  //cout << constraintStream.str() << endl;
                                  
                                  break;
                          }
		  default :
			  {
				  break;
			  }
	  }

  }

  assertStream << "(assert (forall (" << varStream.str() << ") (and " << constraintStream.str() << ")))\n";

  funStream << "(define-fun " << funName <<" (" << varStream.str() << ") " << funSort.str() << " ";

  //cout << variableStream.str() << endl;
  //cout << funStream.str() << endl;
  //cout << assertStream.str() << endl;


  vector<string> Q;
  vector< vector<string> > waitList;
  vector< vector<string> > finalList;

  Q.push_back(nonTerminalInfo[0]);

  //Prioritize productions
  for(uint32_t i = 0; i < priortyOrderProductions.size(); i++)
  {
      string lhs = priortyOrderProductions[i][0];
      string rhs = priortyOrderProductions[i][1];
 
      string tempStr = rhs;
 
      while(true)
      {
          if ( (tempStr.find("{") == string::npos) | ((tempStr.find("}") == string::npos))) 
          {
              //Move production to Final List
              finalList.push_back(priortyOrderProductions[i]);

              //Check if lhs is in Q, if not add lhs to Q
              if(find(Q.begin(), Q.end(), lhs) == Q.end())
              {
                   Q.push_back(lhs);
              }

              break;
          }
        
          size_t pos1 = tempStr.find("{");
 
          size_t pos2 = tempStr.find("}");
        
          string subStr = tempStr.substr(pos1 , (pos2-pos1+1));
        
          //Check if subStr (<..>) is in Q, if not add subStr to Q
          if(find(Q.begin(), Q.end(), subStr) == Q.end())
          {
               // Move production to waitList
               waitList.push_back(priortyOrderProductions[i]);

               break;
          }
        
          tempStr = tempStr.substr(pos2+1);
      }

  }

  /*
  for(int i = (nonTerminalInfo.size()-1); i >= 0; i--)
  {
      for(uint32_t j = 0; j < waitList.size(); j++)
      {
          if(nonTerminalInfo[i] == waitList[j][0])
           {
                finalList.push_back(waitList[j]);
           }
      }

  }
  */

  finalList.insert(finalList.end(), waitList.begin(), waitList.end());

  priortyOrderProductions.clear();

  priortyOrderProductions.insert(priortyOrderProductions.end(), finalList.begin(), finalList.end());

/*
  for(uint32_t i = 0; i < priortyOrderProductions.size(); i++)
  {
     cout << priortyOrderProductions[i][0] << " -> " << priortyOrderProductions[i][1] << endl;
  }
*/

  uint32_t progSize = 1;
  vector<string> C;

  while(true)
  {
	  C.clear();

	  C = enumerateExpForAllProduction(E, nonTerminalInfo, priortyOrderProductions);

	  for(uint32_t i=0; i < C.size(); i++)
	  {
	       //cout << C[i] << endl;

               if(doesExprSatisfiesPoints(C[i]) == false)
               {
                    continue;
               }

               stringstream z3ProgramStream;

               z3ProgramStream << variableStream.str() << funStream.str() << C[i] << ")\n" << assertStream.str() << "(check-sat)";

               //cout << z3ProgramStream.str() << endl;

               if(checkExprAgainstSpec(z3ProgramStream.str()) == true)
               { 
                    cout << "Distinct Counter Example Points generated are: " <<endl;
                    for(uint32_t q = 0; q < points[0].size(); q++)
                    {
                         for(uint32_t p = 0; p < argVar.size(); p++)
                         {
                               cout << argVar[p] <<" = "  << points[p][q] << " ";
                         }

                         cout << endl;
                    }

                    cout << endl;
                    
                    cout << "Hurray! Synthesized Expression is: " << C[i] << endl;

                    remove("model.txt");

                    exit(0);
               }
               else
               {
                    // Add Counter Example to set of points

                    ifstream infile("model.txt");

                    string line;

                    int linecount = 0;

                    uint32_t index;

                    while (getline(infile, line))
                    {
                          if(linecount % 2)
                          {
                               line.erase(remove(line.begin(), line.end(), '('), line.end());
                               line.erase(remove(line.begin(), line.end(), ')'), line.end());
                               //cout << line << endl;

                               bool negate = false;
                               if (line.find('-') != string::npos)
                               {
                                     negate = true;
                                     line.erase(remove(line.begin(), line.end(), '-'), line.end());
                               }

                               //cout << line << endl;

                               istringstream iss(line);
                               int a;
                               iss >> a;

                               if(negate == true)
                                    a = a * (-1);

                               tmpPoints[index].push_back(a);

                               //cout << a << endl;
                          }
                          else
                          {
                               //cout << line << endl;

                               for(uint32_t j = 0; j < argVar.size(); j++)
                               {
                                    if (line.find(argVar[j]) != string::npos)
                                    {
                                        index = j;
                                        break;
                                        //cout << line << endl;
                                        //cout << "found " << argVar[j] << '\n';
                                    }
                               }
                          }

                          linecount ++;

                          // process pair (a,b)
                    }

                    bool flag = true;

                    for(uint32_t j = 0; j < argVar.size(); j++)
                    {
                       if(find(points[j].begin(), points[j].end(), tmpPoints[j][0]) != points[j].end())
                       {
                            flag = flag & true;
                       }
                       else
                       {
                            flag = flag & false;
                       }
                    }

                    if(!flag)
                    {
                       for(uint32_t j = 0; j < argVar.size(); j++)
                       {
                              points[j].push_back(tmpPoints[j][0]);
                       }
                    }

                    for(uint32_t j = 0; j < argVar.size(); j++)
                    {
                        tmpPoints[j].clear();
                    }

                    infile.close();

               }

               //cout <<  endl;

               if(checkEquivalance(C[i]) == false)
               {
                    E.push_back(C[i]); //Appending expression to E
               }
 
	  }

          progSize ++;

          if(progSize > 1)
          {
               break;
          }
  }

  delete Parser;

  return 0;
}
