CXX  = g++ -std=c++11
DIR  = /usr/local/Cellar/gecode/6.1.1
LIBS = -lgecodedriver    -lgecodesearch  \
       -lgecodeminimodel -lgecodeint     \
       -lgecodekernel    -lgecodesupport

p: project.cpp
	$(CXX) -I$(DIR)/include -c project.cpp
	$(CXX) -L$(DIR)/lib -o p project.o $(LIBS)
