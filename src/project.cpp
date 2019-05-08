#include <fstream>
#include <vector>
#include <iostream>
#include <string>
#include <gecode/driver.hh>
#include <gecode/int.hh>
#include <gecode/minimodel.hh>
#include <gecode/search.hh>

using namespace std;
using namespace Gecode;

//typedef int rows;
//typedef vector<int> table;
typedef vector<int> VI;
//typedef VI[int][int];
//typedef vector<VI>  VVI;
//#define IN 10;


class CircuitSynthesis : public Space {

private:
  int numberRows;
  int numberVars;
  int numberElements;
  int numberNodes;
  int depth;
  int numberItemsTree;

protected:
  IntVarArray c;
  BoolVarArray indicator;
  BoolVarArray body;
  //BoolVarArray node;
  //BoolVarArray channel;

public:
  CircuitSynthesis(const VI& g, const int numberRowsIn, const int numberVarsIn, const int numberNodesIn, const int numberElementsIn, const int depthIn) : numberRows(numberRowsIn), numberVars(numberVarsIn), numberNodes(numberNodesIn), depth(depthIn), numberElements(numberElementsIn), numberItemsTree(numberElements + numberNodes), c(*this, numberItemsTree, -2, numberVars), indicator(*this, (numberItemsTree)*(numberVars + 1),0,1), body(*this, (numberItemsTree)*numberRows,0,1){
    bool arrayTable[numberVars][numberRows];
    int array0[numberRows];
    //int arrayDefault[numberRows];
    // switch(depth){
    //   case 0:

    // }
    // Initialize arrays (Is it necessary?)
    for(int i = 0; i < numberRows; ++i)
      array0[i] = 0;

    // for(int i = 0; i < numberRows; ++i)
    //   arrayDefault[i] = -1;

    for(int i = 0; i < numberRows; ++i){
      for(int j = 0; j < numberVars; ++j){
        arrayTable[i][j] = 0;
      } 
    }

    // Building truth table
    for (int u = 0; u < numberRows; ++u){
      int n = u;
      for (int k = 0; k < numberVars; ++k){
        arrayTable[u][numberVars - 1 - k] = n % 2;
        n = n/2;
      }
      arrayTable[numberVars][u] = g[u];
    }

    

    // Extension sequences
    // TupleSet td(numberRows);
    // td.add(IntArgs(numberRows, arrayDefault));
    // td.finalize();

    TupleSet t0(numberRows);
    t0.add(IntArgs(numberRows,array0));
    t0.finalize();

    TupleSet t1(numberRows);
    int array1[numberRows];
      for(int j = 0; j < numberRows; ++j){
        array1[j] = arrayTable[j][0];
        //cout << array1[j] << endl;
      }
      t1.add(IntArgs(numberRows,array1));
    t1.finalize();

    // cout << t1[0] << endl;

    TupleSet t2(numberRows);
    int array2[numberRows];
      for(int j = 0; j < numberRows; ++j){
        array2[j] = arrayTable[j][1];
        //cout << array2[j] << endl;
      }
      t2.add(IntArgs(numberRows,array2));
    t2.finalize();

    TupleSet t3(numberRows);
    int array3[numberRows];
    if (numberVars > 2){
      for(int j = 0; j < numberRows; ++j){
        array3[j] = arrayTable[j][2];
        //cout << array2[j] << endl;
      }
      t3.add(IntArgs(numberRows,array3));
    }
    t3.finalize();
    //Show truth table (for validation purposes)
    // cout << "Truth Table: " << endl;
    // for(int i = 0; i < numberRows; ++i){
    //   for(int j = 0; j < numberVars; ++j){
    //     cout << arrayTable[i][j] << " ";
    //   }
    //   cout << " = " << g[i] << endl;
    // }   

    Matrix<BoolVarArray> matIndicator(indicator, numberItemsTree, numberVars + 1);
    Matrix<BoolVarArray> matBody(body, numberItemsTree, numberRows);
    // Matrix<BoolVarArray> matChannel(channel, numberNodes, numberRows);
    //cout << "matrix" << endl;
    for(int i = 0; i < numberItemsTree; ++i){
      extensional(*this, matBody.col(i), t0, imp(matIndicator(i,0)));
      extensional(*this, matBody.col(i), t1, imp(matIndicator(i,1)));
      extensional(*this, matBody.col(i), t2, imp(matIndicator(i,2)));
      if (numberVars > 2){
        extensional(*this, matBody.col(i), t3, imp(matIndicator(i,3)));
      }
      //extensional(*this, matBody.col(i), td, imp(matIndicator(i,3)));
    }
    //cout << " eq" << endl;
    for(int i = 0; i < numberItemsTree; ++i){
      rel(*this, c[i], IRT_EQ, 0, matIndicator(i,0));
      rel(*this, c[i], IRT_EQ, 1, matIndicator(i,1));
      rel(*this, c[i], IRT_EQ, 2, matIndicator(i,2));
      if (numberVars > 2){
        rel(*this, c[i], IRT_EQ, 3, matIndicator(i,3));
      }
      
    }
    if (depth == 0){
      //cout << "0 0" << endl;
      rel(*this, sum(matIndicator.col(0)) == 1);
      //rel(*this, c[0] >= 0);
    }

      
    //Cases

    if(depth == 1){
      //cout << "1 1" << endl;
      rel(*this, sum(matIndicator.col(1)) == 1);
      rel(*this, sum(matIndicator.col(2)) == 1);
      //rel(*this, sum(matIndicator.col(0)) == 0);
      for(int row = 0; row < numberRows; ++row){
        rel(*this, matBody(0,row) == !(matBody(1,row) || matBody(2,row)));
      }
      rel(*this, c[0], IRT_EQ, -1);
      //rel(*this, )
    }

    if(depth == 2 && numberNodes == 2){
      rel(*this, sum(matIndicator.col(2)) == 1);
      rel(*this, sum(matIndicator.col(3)) == 1);
      rel(*this, sum(matIndicator.col(4)) == 1);
      //rel(*this, sum(matIndicator.col(0)) == 0);
      for(int row = 0; row < numberRows; ++row){
        rel(*this, matBody(0,row) == !(matBody(1,row) || matBody(2,row)));
        rel(*this, matBody(1,row) == !(matBody(3,row) || matBody(4,row)));
      }
      rel(*this, c[0], IRT_EQ, -1);
      rel(*this, c[1], IRT_EQ, -1);
    }

    if(depth == 2 && numberNodes == 3){
      //rel(*this, sum(matIndicator.col(2)) == 1);
      rel(*this, sum(matIndicator.col(3)) == 1);
      rel(*this, sum(matIndicator.col(4)) == 1);
      rel(*this, sum(matIndicator.col(5)) == 1);
      rel(*this, sum(matIndicator.col(6)) == 1);
      //rel(*this, sum(matIndicator.col(0)) == 0);
      for(int row = 0; row < numberRows; ++row){
        rel(*this, matBody(0,row) == !(matBody(1,row) || matBody(2,row)));
        rel(*this, matBody(1,row) == !(matBody(3,row) || matBody(4,row)));
        rel(*this, matBody(2,row) == !(matBody(5,row) || matBody(6,row)));
      }
      rel(*this, c[0], IRT_EQ, -1);
      rel(*this, c[1], IRT_EQ, -1);
      rel(*this, c[2], IRT_EQ, -1);
    }

    if(depth == 3 && numberNodes == 3){
      //cout << "3 3" << endl;
      rel(*this, sum(matIndicator.col(4)) == 1);
      rel(*this, sum(matIndicator.col(7)) == 1);
      rel(*this, sum(matIndicator.col(8)) == 1);
      rel(*this, sum(matIndicator.col(2)) == 1);
      for(int row = 0; row < numberRows; ++row){
        rel(*this, matBody(0,row) == !(matBody(1,row) || matBody(2,row)));
        rel(*this, matBody(1,row) == !(matBody(3,row) || matBody(4,row)));
        rel(*this, matBody(3,row) == !(matBody(7,row) || matBody(8,row)));
      }
      rel(*this, c[0], IRT_EQ, -1);
      rel(*this, c[1], IRT_EQ, -1);
      rel(*this, c[3], IRT_EQ, -1);
    }

    if(depth == 3 && numberNodes == 4){
      //cout << "honk" << endl;
      //rel(*this, sum(matIndicator.col(4)) == 1);
      //rel(*this, sum(matIndicator.col(5)) == 1);
      //rel(*this, sum(matIndicator.col(6)) == 1);
      rel(*this, sum(matIndicator.col(7)) == 1);
      rel(*this, sum(matIndicator.col(8)) == 1);
      rel(*this, sum(matIndicator.col(2)) == 1);
      rel(*this, sum(matIndicator.col(9)) == 1);
      rel(*this, sum(matIndicator.col(10)) == 1);

      for(int row = 0; row < numberRows; ++row){
        
         rel(*this, matBody(0,row) == !(matBody(1,row) || matBody(2,row)));
         rel(*this, matBody(1,row) == !(matBody(3,row) || matBody(4,row)));
         //rel(*this, matBody(2,row) == !(matBody(5,row) || matBody(6,row)));
         rel(*this, matBody(3,row) == !(matBody(7,row) || matBody(8,row)));
         rel(*this, matBody(4,row) == !(matBody(9,row) || matBody(10,row)));
      }
      rel(*this, c[0], IRT_EQ, -1);
      rel(*this, c[1], IRT_EQ, -1);
      rel(*this, c[3], IRT_EQ, -1);
      rel(*this, c[4], IRT_EQ, -1);
    }

    if(depth == 3 && numberNodes == 5){
      //cout << "3 5" << endl;
      //rel(*this, sum(matIndicator.col(4)) == 1);
      //rel(*this, sum(matIndicator.col(5)) == 1);
      //rel(*this, sum(matIndicator.col(6)) == 1);
      rel(*this, sum(matIndicator.col(7)) == 1);
      rel(*this, sum(matIndicator.col(8)) == 1);
      rel(*this, sum(matIndicator.col(5)) == 1);
      rel(*this, sum(matIndicator.col(6)) == 1);
      rel(*this, sum(matIndicator.col(9)) == 1);
      rel(*this, sum(matIndicator.col(10)) == 1);

      for(int row = 0; row < numberRows; ++row){
        
         rel(*this, matBody(0,row) == !(matBody(1,row) || matBody(2,row)));
         rel(*this, matBody(1,row) == !(matBody(3,row) || matBody(4,row)));
         rel(*this, matBody(2,row) == !(matBody(5,row) || matBody(6,row)));
         rel(*this, matBody(3,row) == !(matBody(7,row) || matBody(8,row)));
         rel(*this, matBody(4,row) == !(matBody(9,row) || matBody(10,row)));
      }

      rel(*this, c[0], IRT_EQ, -1);
      rel(*this, c[1], IRT_EQ, -1);
      rel(*this, c[2], IRT_EQ, -1);
      rel(*this, c[3], IRT_EQ, -1);
      rel(*this, c[4], IRT_EQ, -1);
    }

     if(depth == 3 && numberNodes == 6){
      //cout << "3 6" << endl;
      //rel(*this, sum(matIndicator.col(4)) == 1);
      //rel(*this, sum(matIndicator.col(5)) == 1);
      rel(*this, sum(matIndicator.col(6)) == 1);
      rel(*this, sum(matIndicator.col(7)) == 1);
      rel(*this, sum(matIndicator.col(8)) == 1);
      rel(*this, sum(matIndicator.col(9)) == 1);
      rel(*this, sum(matIndicator.col(10)) == 1);
      rel(*this, sum(matIndicator.col(11)) == 1);
      rel(*this, sum(matIndicator.col(12)) == 1);

      for(int row = 0; row < numberRows; ++row){
        
         rel(*this, matBody(0,row) == !(matBody(1,row) || matBody(2,row)));
         rel(*this, matBody(1,row) == !(matBody(3,row) || matBody(4,row)));
         rel(*this, matBody(2,row) == !(matBody(5,row) || matBody(6,row)));
         rel(*this, matBody(3,row) == !(matBody(7,row) || matBody(8,row)));
         rel(*this, matBody(4,row) == !(matBody(9,row) || matBody(10,row)));
         rel(*this, matBody(5,row) == !(matBody(11,row) || matBody(12,row)));
      }

      rel(*this, c[0], IRT_EQ, -1);
      rel(*this, c[1], IRT_EQ, -1);
      rel(*this, c[2], IRT_EQ, -1);
      rel(*this, c[3], IRT_EQ, -1);
      rel(*this, c[4], IRT_EQ, -1);
      rel(*this, c[5], IRT_EQ, -1);
    }

     if(depth == 3 && numberNodes == 7){
      //cout << "3 7" << endl;

      rel(*this, sum(matIndicator.col(7)) == 1);
      rel(*this, sum(matIndicator.col(8)) == 1);
      rel(*this, sum(matIndicator.col(9)) == 1);
      rel(*this, sum(matIndicator.col(10)) == 1);
      rel(*this, sum(matIndicator.col(11)) == 1);
      rel(*this, sum(matIndicator.col(12)) == 1);
      rel(*this, sum(matIndicator.col(13)) == 1);
      rel(*this, sum(matIndicator.col(14)) == 1);

      for(int row = 0; row < numberRows; ++row){
        
         rel(*this, matBody(0,row) == !(matBody(1,row) || matBody(2,row)));
         rel(*this, matBody(1,row) == !(matBody(3,row) || matBody(4,row)));
         rel(*this, matBody(2,row) == !(matBody(5,row) || matBody(6,row)));
         rel(*this, matBody(3,row) == !(matBody(7,row) || matBody(8,row)));
         rel(*this, matBody(4,row) == !(matBody(9,row) || matBody(10,row)));
         rel(*this, matBody(5,row) == !(matBody(11,row) || matBody(12,row)));
         rel(*this, matBody(6,row) == !(matBody(13,row) || matBody(14,row)));
      }

      rel(*this, c[0], IRT_EQ, -1);
      rel(*this, c[1], IRT_EQ, -1);
      rel(*this, c[2], IRT_EQ, -1);
      rel(*this, c[3], IRT_EQ, -1);
      rel(*this, c[4], IRT_EQ, -1);
      rel(*this, c[5], IRT_EQ, -1);
      rel(*this, c[6], IRT_EQ, -1);
    }

      if(depth == 4 && numberNodes == 8){
      //cout << "4 8" << endl;

      //rel(*this, sum(matIndicator.col(7)) == 1);
      rel(*this, sum(matIndicator.col(8)) == 1);
      rel(*this, sum(matIndicator.col(9)) == 1);
      rel(*this, sum(matIndicator.col(10)) == 1);
      rel(*this, sum(matIndicator.col(11)) == 1);
      rel(*this, sum(matIndicator.col(12)) == 1);
      rel(*this, sum(matIndicator.col(13)) == 1);
      rel(*this, sum(matIndicator.col(14)) == 1);
      rel(*this, sum(matIndicator.col(15)) == 1);
      rel(*this, sum(matIndicator.col(16)) == 1);

      for(int row = 0; row < numberRows; ++row){
        
         rel(*this, matBody(0,row) == !(matBody(1,row) || matBody(2,row)));
         rel(*this, matBody(1,row) == !(matBody(3,row) || matBody(4,row)));
         rel(*this, matBody(2,row) == !(matBody(5,row) || matBody(6,row)));
         rel(*this, matBody(3,row) == !(matBody(7,row) || matBody(8,row)));
         rel(*this, matBody(4,row) == !(matBody(9,row) || matBody(10,row)));
         rel(*this, matBody(5,row) == !(matBody(11,row) || matBody(12,row)));
         rel(*this, matBody(6,row) == !(matBody(13,row) || matBody(14,row)));
         rel(*this, matBody(7,row) == !(matBody(15,row) || matBody(16,row)));
      }

      rel(*this, c[0], IRT_EQ, -1);
      rel(*this, c[1], IRT_EQ, -1);
      rel(*this, c[2], IRT_EQ, -1);
      rel(*this, c[3], IRT_EQ, -1);
      rel(*this, c[4], IRT_EQ, -1);
      rel(*this, c[5], IRT_EQ, -1);
      rel(*this, c[6], IRT_EQ, -1);
      rel(*this, c[7], IRT_EQ, -1);
    }

  
    if(depth == 4 && numberNodes == 6){
      //cout << "4 6" << endl;

      rel(*this, sum(matIndicator.col(7)) == 1);
      rel(*this, sum(matIndicator.col(8)) == 1);
      rel(*this, sum(matIndicator.col(9)) == 1);
      rel(*this, sum(matIndicator.col(10)) == 1);
      rel(*this, sum(matIndicator.col(11)) == 1);
      rel(*this, sum(matIndicator.col(12)) == 1);
      rel(*this, sum(matIndicator.col(6)) == 1);
   

      for(int row = 0; row < numberRows; ++row){
        
         rel(*this, matBody(0,row) == !(matBody(1,row) || matBody(2,row)));
         rel(*this, matBody(1,row) == !(matBody(3,row) || matBody(4,row)));
         rel(*this, matBody(2,row) == !(matBody(5,row) || matBody(6,row)));
         rel(*this, matBody(3,row) == !(matBody(7,row) || matBody(8,row)));
         rel(*this, matBody(4,row) == !(matBody(9,row) || matBody(10,row)));
         rel(*this, matBody(5,row) == !(matBody(11,row) || matBody(12,row)));
         
      }

      rel(*this, c[0], IRT_EQ, -1);
      rel(*this, c[1], IRT_EQ, -1);
      rel(*this, c[2], IRT_EQ, -1);
      rel(*this, c[3], IRT_EQ, -1);
      rel(*this, c[4], IRT_EQ, -1);
      rel(*this, c[5], IRT_EQ, -1);
    }
  
   if(depth == 4 && numberNodes == 7){
      //cout << "4 7" << endl;

      rel(*this, sum(matIndicator.col(7)) == 1);
      rel(*this, sum(matIndicator.col(8)) == 1);
      rel(*this, sum(matIndicator.col(9)) == 1);
      rel(*this, sum(matIndicator.col(10)) == 1);
      rel(*this, sum(matIndicator.col(11)) == 1);
      rel(*this, sum(matIndicator.col(12)) == 1);
      rel(*this, sum(matIndicator.col(13)) == 1);
      rel(*this, sum(matIndicator.col(14)) == 1);
   

      for(int row = 0; row < numberRows; ++row){
        
         rel(*this, matBody(0,row) == !(matBody(1,row) || matBody(2,row)));
         rel(*this, matBody(1,row) == !(matBody(3,row) || matBody(4,row)));
         rel(*this, matBody(2,row) == !(matBody(5,row) || matBody(6,row)));
         rel(*this, matBody(3,row) == !(matBody(7,row) || matBody(8,row)));
         rel(*this, matBody(4,row) == !(matBody(9,row) || matBody(10,row)));
         rel(*this, matBody(5,row) == !(matBody(11,row) || matBody(12,row)));
         rel(*this, matBody(6,row) == !(matBody(13,row) || matBody(14,row)));
      }

      rel(*this, c[0], IRT_EQ, -1);
      rel(*this, c[1], IRT_EQ, -1);
      rel(*this, c[2], IRT_EQ, -1);
      rel(*this, c[3], IRT_EQ, -1);
      rel(*this, c[4], IRT_EQ, -1);
      rel(*this, c[5], IRT_EQ, -1);
      rel(*this, c[6], IRT_EQ, -1);
    }


  if(depth == 4 && numberNodes == 9){
      //cout << "4 9" << endl;

      //rel(*this, sum(matIndicator.col(7)) == 1);
      rel(*this, sum(matIndicator.col(8)) == 1);
      //rel(*this, sum(matIndicator.col(9)) == 1);
      rel(*this, sum(matIndicator.col(10)) == 1);
      rel(*this, sum(matIndicator.col(11)) == 1);
      rel(*this, sum(matIndicator.col(12)) == 1);
      rel(*this, sum(matIndicator.col(13)) == 1);
      rel(*this, sum(matIndicator.col(14)) == 1);
      rel(*this, sum(matIndicator.col(15)) == 1);
      rel(*this, sum(matIndicator.col(16)) == 1);
      rel(*this, sum(matIndicator.col(19)) == 1);
      rel(*this, sum(matIndicator.col(20)) == 1);

      for(int row = 0; row < numberRows; ++row){
        
         rel(*this, matBody(0,row) == !(matBody(1,row) || matBody(2,row)));
         rel(*this, matBody(1,row) == !(matBody(3,row) || matBody(4,row)));
         rel(*this, matBody(2,row) == !(matBody(5,row) || matBody(6,row)));
         rel(*this, matBody(3,row) == !(matBody(7,row) || matBody(8,row)));
         rel(*this, matBody(4,row) == !(matBody(9,row) || matBody(10,row)));
         rel(*this, matBody(5,row) == !(matBody(11,row) || matBody(12,row)));
         rel(*this, matBody(6,row) == !(matBody(13,row) || matBody(14,row)));
         rel(*this, matBody(7,row) == !(matBody(15,row) || matBody(16,row)));
         rel(*this, matBody(9,row) == !(matBody(19,row) || matBody(20,row)));
      }

      rel(*this, c[0], IRT_EQ, -1);
      rel(*this, c[1], IRT_EQ, -1);
      rel(*this, c[2], IRT_EQ, -1);
      rel(*this, c[3], IRT_EQ, -1);
      rel(*this, c[4], IRT_EQ, -1);
      rel(*this, c[5], IRT_EQ, -1);
      rel(*this, c[6], IRT_EQ, -1);
      rel(*this, c[7], IRT_EQ, -1);
      rel(*this, c[9], IRT_EQ, -1);
    }

    if(depth == 4 && numberNodes == 10){
      //cout << "4 10" << endl;

      //rel(*this, sum(matIndicator.col(7)) == 1);
      rel(*this, sum(matIndicator.col(8)) == 1);
      //rel(*this, sum(matIndicator.col(9)) == 1);
      rel(*this, sum(matIndicator.col(10)) == 1);
      //rel(*this, sum(matIndicator.col(11)) == 1);
      rel(*this, sum(matIndicator.col(12)) == 1);
      rel(*this, sum(matIndicator.col(13)) == 1);
      rel(*this, sum(matIndicator.col(14)) == 1);
      rel(*this, sum(matIndicator.col(15)) == 1);
      rel(*this, sum(matIndicator.col(16)) == 1);
      rel(*this, sum(matIndicator.col(19)) == 1);
      rel(*this, sum(matIndicator.col(20)) == 1);
      rel(*this, sum(matIndicator.col(23)) == 1);
      rel(*this, sum(matIndicator.col(24)) == 1);

      for(int row = 0; row < numberRows; ++row){
        
         rel(*this, matBody(0,row) == !(matBody(1,row) || matBody(2,row)));
         rel(*this, matBody(1,row) == !(matBody(3,row) || matBody(4,row)));
         rel(*this, matBody(2,row) == !(matBody(5,row) || matBody(6,row)));
         rel(*this, matBody(3,row) == !(matBody(7,row) || matBody(8,row)));
         rel(*this, matBody(4,row) == !(matBody(9,row) || matBody(10,row)));
         rel(*this, matBody(5,row) == !(matBody(11,row) || matBody(12,row)));
         rel(*this, matBody(6,row) == !(matBody(13,row) || matBody(14,row)));
         rel(*this, matBody(7,row) == !(matBody(15,row) || matBody(16,row)));
         rel(*this, matBody(9,row) == !(matBody(19,row) || matBody(20,row)));
         rel(*this, matBody(11,row) == !(matBody(23,row) || matBody(24,row)));

      }

      rel(*this, c[0], IRT_EQ, -1);
      rel(*this, c[1], IRT_EQ, -1);
      rel(*this, c[2], IRT_EQ, -1);
      rel(*this, c[3], IRT_EQ, -1);
      rel(*this, c[4], IRT_EQ, -1);
      rel(*this, c[5], IRT_EQ, -1);
      rel(*this, c[6], IRT_EQ, -1);
      rel(*this, c[7], IRT_EQ, -1);
      rel(*this, c[9], IRT_EQ, -1);
      rel(*this, c[11], IRT_EQ, -1);
    }
    

    //Result
    rel(*this, matBody.col(0), IRT_EQ, g);

    //Search 
    branch(*this, c, INT_VAR_NONE(), INT_VAL_MIN());
    //branch(*this, body, BOOL_VAR_NONE(), BOOL_VAL_MAX());
    //branch(*this, indicator, BOOL_VAR_NONE(), BOOL_VAL_MAX());
  }

  CircuitSynthesis(CircuitSynthesis& s) : Space(s) {
    numberRows = s.numberRows;
    numberVars = s.numberVars;
    numberNodes = s.numberNodes;
    numberElements = s.numberElements;
    numberItemsTree = s.numberItemsTree;
    depth = s.depth;
    //d = s.d;
    c.update(*this, s.c);
    indicator.update(*this, s.indicator);
    body.update(*this, s.body);
    //node.update(*this, s.node);
    // channel.update(*this, s.channel);
    // //body.update(*this, s.body);
    // //result.update(*this, s.result);
    // isNode.update(*this, s.isNode);
    // isVar.update(*this, s.isVar);
  }

  virtual Space* copy() {
    return new CircuitSynthesis(*this);
  }

  

  void print(void) const {
    bool control = false;
    int countNOR = 0;
    for(int i = 0; i < c.size(); ++i){
      int base = c[i].val();
      if (base != -2)
        control = true;
      if (base == -1)
        ++countNOR;
    }
    if (control == false){
      cout << -2 << endl;
      cout << -2 << endl;
    }

    cout << depth << " " << countNOR << " " << endl;
    for(int i = 0; i < c.size(); ++i){
      if (c[i].val() == 0){
        cout << i + 1 << " 0 0 0" << endl;
      }
      else if(c[i].val() == -1){
        cout << i + 1 << " -1 " << (i + 1) + (i + 1) << " " << (i + 1) + (i + 1) + 1 << endl;
      }
      
    }
    
  }

  virtual void constrain(const Space& _b) {

  }
};


int main(int argc, char* argv[]) {
  try {
    if (argc != 2) return 1;
    ifstream in(argv[1]);
    
    int n;
    in >> n;

    cout << n << endl;

    int rows = pow(2,n);
    vector<int> table(rows);
    //cout << "Number of variables: " << n << endl;
    //cout << "Size of truth table: " << rows << endl;
    for (int k = 0; k < rows; ++k) {
      int now;
      in >> now;
      table[k] = now;

      cout << now << endl;
      
    }
    int nodes = 0;
    int elements = 30;
    int depth = 0;
    int environment = 0;
    //int numberNodes = 3;
    
    //delete mod;
    CircuitSynthesis* sant;// = e.next();
    CircuitSynthesis* mod;
    while(sant == NULL && environment <= 12){
      if (environment == 1){
        depth = 1;
        nodes = 1;
      }
      if (environment == 2){
        depth = 2;
        nodes = 2;
      }
      if (environment == 3){
        depth = 2;
        nodes = 3;
      }
      if (environment == 4){
        depth = 3;
        nodes = 3;
      }
      if (environment == 5){
        depth = 3;
        nodes = 4;
      }
      if (environment == 6){
        depth = 3;
        nodes = 5;
      }
      if (environment == 7){
        depth = 3;
        nodes = 6;
      }
      if (environment == 8){
        depth = 3;
        nodes = 7;
      }
      if (environment == 9){
        depth = 4;
        nodes = 8;
      }
      if (environment == 10){
        depth = 4;
        nodes = 9;
      }
      if (environment == 11){
        depth = 4;
        nodes = 10;
      }
      if (environment == 12){
        depth = 4;
        nodes = 6;
      }
     

      mod = new CircuitSynthesis(table, rows, n, nodes, elements, depth);
      //delete mod;
      BAB<CircuitSynthesis> e(mod);
      sant = e.next();
      ++environment;
    }
    //cout << in << endl;
    //cout << argv[1] << "\t\t";
    sant->print();
    //cout << argv[1] << '\t' << sant->moreinfo() << endl;
    delete sant;
    delete mod;
    
  }
  catch (Exception e) {
    cerr << "Gecode exception: " << e.what() << endl;
    return 1;
  }
  return 0;
}
