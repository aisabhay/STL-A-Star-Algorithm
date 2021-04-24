
// A* Algorithm Implementation using STL

#include <iostream>

// STL includes
#include <algorithm> // includes functions to create heap and perform push, pop and sort operations
#include <vector>
#include <cfloat>

using namespace std;

// A* Algorithm Code Starts -----------------------------------------------------------------------------------------------------------

template <class UserState> class AStarSearch // The A* search class. UserState is used to retrieve data of a particular state.
{

public: // data

	enum
	{
		SEARCH_STATE_NOT_INITIALISED,
		SEARCH_STATE_SEARCHING,
		SEARCH_STATE_SUCCEEDED,
		SEARCH_STATE_FAILED,
	};

	public:

	class Node // A node represents a possible state in the search.
    {
        public:
            Node *parent; // used during the search to record the parent of successor nodes
			Node *child; // used after the search for the application to view the search in reverse
			float g; // cost of this node + it's predecessors
			float h; // heuristic estimate of distance to goal
			float f; // sum of cumulative cost of predecessors and self and heuristic
			Node() :
				parent( 0 ),
				child( 0 ),
				g( 0.0f ),
				h( 0.0f ),
				f( 0.0f )
			{}
            UserState m_UserState;
	};

    class HeapCompare_f // For sorting the heap the STL needs compare function that lets us compare the f value of two nodes
	{
		public:

			bool operator() ( const Node *x, const Node *y ) const
			{
				return x->f > y->f;
			}
	};


public: // methods


	// constructor just initializes private data
	AStarSearch() :
		m_State( SEARCH_STATE_NOT_INITIALISED ),
		m_CurrentSolutionNode( NULL ),
		m_AllocateNodeCount(0)
	{
	}

	// Set Start and goal states
	void SetStartAndGoalStates( UserState &Start, UserState &Goal )
	{


		m_Start = AllocateNode();
		m_Goal = AllocateNode();
		m_Start->m_UserState = Start;
		m_Goal->m_UserState = Goal;

		m_State = SEARCH_STATE_SEARCHING;

		// Initialize the AStar specific parts of the Start Node. The user only needs fill out the state information.

		m_Start->g = 0;
		m_Start->h = m_Start->m_UserState.GoalDistanceEstimate( m_Goal->m_UserState );
		m_Start->f = m_Start->g + m_Start->h;
		m_Start->parent = 0;

		// Push the start node on the Open list
        m_OpenList.push_back( m_Start ); // heap now unsorted

		// Sort back element into heap
		push_heap( m_OpenList.begin(), m_OpenList.end(), HeapCompare_f() );

		// Initialize counter for search steps
		m_Steps = 0;
	}

	// Advances search one step
	unsigned int SearchStep()
	{

		// Next we want it to be safe to do a search step once the search has succeeded...
		if( (m_State == SEARCH_STATE_SUCCEEDED) || (m_State == SEARCH_STATE_FAILED) )
		{
			return m_State;
		}

		// Increment step count
		m_Steps ++;

		// Pop the best node (the one with the lowest f)
		Node *n = m_OpenList.front(); // get pointer to the node
		pop_heap( m_OpenList.begin(), m_OpenList.end(), HeapCompare_f() );
		m_OpenList.pop_back();

		// Check for the goal, once we pop that we're done
		if( n->m_UserState.IsGoal( m_Goal->m_UserState ) )
		{
			// The user is going to use the Goal Node he passed in so copy the parent pointer of n
			m_Goal->parent = n->parent;
			m_Goal->g = n->g;

			// A special case is that the goal was passed in as the start state so handle that here
			if( false == n->m_UserState.IsSameState( m_Start->m_UserState ) )
			{
				FreeNode( n );

				// set the child pointers in each node (except Goal which has no child)
				Node *nodeChild = m_Goal;
				Node *nodeParent = m_Goal->parent;

				do
				{
					nodeParent->child = nodeChild;

					nodeChild = nodeParent;
					nodeParent = nodeParent->parent;

				}
				while( nodeChild != m_Start ); // Start is always the first node by definition

			}

			// delete nodes that are not needed for the solution
			FreeUnusedNodes();

			m_State = SEARCH_STATE_SUCCEEDED;

			return m_State;
		}
		else // not goal
		{

			// We now need to generate the successors of this node.

			m_Successors.clear(); // empty vector of successor nodes of n

			bool ret = n->m_UserState.GetSuccessors( this, n->parent ? &n->parent->m_UserState : NULL );

			n->m_UserState.PrintNodeInfo();
			cout << " is selected for Expansion\n\n";

			// Now handle each successor to the current node ...
			for( typename vector< Node * >::iterator successor = m_Successors.begin(); successor != m_Successors.end(); successor ++ )
			{

				// 	The g value for this successor ...
				float newg = n->g + n->m_UserState.GetCost( (*successor)->m_UserState );

				// Now we need to find whether the node is on the open or closed lists If it is but the node that is already on them is better (lower g) then we can forget about this successor

				// First linear search of open list to find node

				typename vector< Node * >::iterator openlist_result;

				for( openlist_result = m_OpenList.begin(); openlist_result != m_OpenList.end(); openlist_result ++ )
				{
					if( (*openlist_result)->m_UserState.IsSameState( (*successor)->m_UserState ) )
					{
						break;
					}
				}

				if( openlist_result != m_OpenList.end() )
				{

					// we found this state on open

					if( (*openlist_result)->g <= newg )
					{
						FreeNode( (*successor) );

						// the one on Open is cheaper than this one
						continue;
					}
				}

				typename vector< Node * >::iterator closedlist_result;

				for( closedlist_result = m_ClosedList.begin(); closedlist_result != m_ClosedList.end(); closedlist_result ++ )
				{
					if( (*closedlist_result)->m_UserState.IsSameState( (*successor)->m_UserState ) )
					{
						break;
					}
				}

				if( closedlist_result != m_ClosedList.end() )
				{

					// we found this state on closed

					if( (*closedlist_result)->g <= newg )
					{
						// the one on Closed is cheaper than this one
						FreeNode( (*successor) );

						continue;
					}
				}

				// This node is the best node so far with this particular state so lets keep it and set up its A* specific data ...

				(*successor)->parent = n;
				(*successor)->g = newg;
				(*successor)->h = (*successor)->m_UserState.GoalDistanceEstimate( m_Goal->m_UserState );
				(*successor)->f = (*successor)->g + (*successor)->h;

				// Successor is in closed list and the new copy is cheaper then
				// 1 - Update old version of this node in closed list
				// 2 - Move it from closed to open list
				// 3 - Sort heap again in open list

				if( closedlist_result != m_ClosedList.end() )
				{
					// Update closed node with successor node AStar data
					(*closedlist_result)->parent = (*successor)->parent;
					(*closedlist_result)->g      = (*successor)->g;
					(*closedlist_result)->h      = (*successor)->h;
					(*closedlist_result)->f      = (*successor)->f;

					// Free successor node
					FreeNode( (*successor) );

					// Push closed node into open list
					m_OpenList.push_back( (*closedlist_result) );

					// Remove closed node from closed list
					m_ClosedList.erase( closedlist_result );

					// Sort back element into heap
					push_heap( m_OpenList.begin(), m_OpenList.end(), HeapCompare_f() );

					// Here we have found a new state which is already CLOSED

				}

				// Successor in open list
				// 1 - Update old version of this node in open list
				// 2 - sort heap again in open list

				else if( openlist_result != m_OpenList.end() )
				{
					// Update open node with successor node AStar data
					(*openlist_result)->parent = (*successor)->parent;
					(*openlist_result)->g      = (*successor)->g;
					(*openlist_result)->h      = (*successor)->h;
					(*openlist_result)->f      = (*successor)->f;

					// Free successor node
					FreeNode( (*successor) );

					// re-make the heap

					make_heap( m_OpenList.begin(), m_OpenList.end(), HeapCompare_f() );
				}

				// New successor
				// 1 - Move it from successors to open list
				// 2 - sort heap again in open list

				else
				{
					// Push successor node into open list
					m_OpenList.push_back( (*successor) );

					// Sort back element into heap
					push_heap( m_OpenList.begin(), m_OpenList.end(), HeapCompare_f() );
				}

			}

			// push n onto Closed, as we have expanded it now

			m_ClosedList.push_back( n );

		} // end else (not goal so expand)

 		return m_State; // Succeeded bool is false at this point.

	}

	// User calls this to add a successor to a list of successors when expanding the search frontier
	bool AddSuccessor( UserState &State )
	{
		Node *node = AllocateNode();

		if( node )
		{
			node->m_UserState = State;

			m_Successors.push_back( node );

			return true;
		}

		return false;
	}

	// Free the solution nodes. This is done to clean up all used Node memory when you are done with the search
	void FreeSolutionNodes()
	{
		Node *n = m_Start;

		if( m_Start->child )
		{
			do
			{
				Node *del = n;
				n = n->child;
				FreeNode( del );

				del = NULL;

			} while( n != m_Goal );

			FreeNode( n ); // Delete the goal

		}
		else
		{
			// if the start node is the solution we need to just delete the start and goal nodes
			FreeNode( m_Start );
			FreeNode( m_Goal );
		}

	}

	// Functions for traversing the solution

	// Get start node
	UserState *GetSolutionStart()
	{
		m_CurrentSolutionNode = m_Start;
		if( m_Start )
		{
			return &m_Start->m_UserState;
		}
		else
		{
			return NULL;
		}
	}

	// Get next node
	UserState *GetSolutionNext()
	{
		if( m_CurrentSolutionNode )
		{
			if( m_CurrentSolutionNode->child )
			{

				Node *child = m_CurrentSolutionNode->child;

				m_CurrentSolutionNode = m_CurrentSolutionNode->child;

				return &child->m_UserState;
			}
		}

		return NULL;
	}

	// Get end node
	UserState *GetSolutionEnd()
	{
		m_CurrentSolutionNode = m_Goal;
		if( m_Goal )
		{
			return &m_Goal->m_UserState;
		}
		else
		{
			return NULL;
		}
	}

	// Step solution iterator backwards
	UserState *GetSolutionPrev()
	{
		if( m_CurrentSolutionNode )
		{
			if( m_CurrentSolutionNode->parent )
			{

				Node *parent = m_CurrentSolutionNode->parent;

				m_CurrentSolutionNode = m_CurrentSolutionNode->parent;

				return &parent->m_UserState;
			}
		}

		return NULL;
	}

	// Get final cost of solution
	// Returns FLTMAX if goal is not defined or there is no solution
	float GetSolutionCost()
	{
		if( m_Goal && m_State == SEARCH_STATE_SUCCEEDED )
		{
			return m_Goal->g;
		}
		else
		{
			return FLT_MAX;
		}
	}

	// For debugging it is useful to be able to view the open and closed list at each step, here are two functions to allow that.

	UserState *GetOpenListStart()
	{
		float f,g,h;
		return GetOpenListStart( f,g,h );
	}

	UserState *GetOpenListStart( float &f, float &g, float &h )
	{
		iterDbgOpen = m_OpenList.begin();
		if( iterDbgOpen != m_OpenList.end() )
		{
			f = (*iterDbgOpen)->f;
			g = (*iterDbgOpen)->g;
			h = (*iterDbgOpen)->h;
			return &(*iterDbgOpen)->m_UserState;
		}

		return NULL;
	}

	UserState *GetOpenListNext()
	{
		float f,g,h;
		return GetOpenListNext( f,g,h );
	}

	UserState *GetOpenListNext( float &f, float &g, float &h )
	{
		iterDbgOpen++;
		if( iterDbgOpen != m_OpenList.end() )
		{
			f = (*iterDbgOpen)->f;
			g = (*iterDbgOpen)->g;
			h = (*iterDbgOpen)->h;
			return &(*iterDbgOpen)->m_UserState;
		}

		return NULL;
	}

	UserState *GetClosedListStart()
	{
		float f,g,h;
		return GetClosedListStart( f,g,h );
	}

	UserState *GetClosedListStart( float &f, float &g, float &h )
	{
		iterDbgClosed = m_ClosedList.begin();
		if( iterDbgClosed != m_ClosedList.end() )
		{
			f = (*iterDbgClosed)->f;
			g = (*iterDbgClosed)->g;
			h = (*iterDbgClosed)->h;

			return &(*iterDbgClosed)->m_UserState;
		}

		return NULL;
	}

	UserState *GetClosedListNext()
	{
		float f,g,h;
		return GetClosedListNext( f,g,h );
	}

	UserState *GetClosedListNext( float &f, float &g, float &h )
	{
		iterDbgClosed++;
		if( iterDbgClosed != m_ClosedList.end() )
		{
			f = (*iterDbgClosed)->f;
			g = (*iterDbgClosed)->g;
			h = (*iterDbgClosed)->h;

			return &(*iterDbgClosed)->m_UserState;
		}

		return NULL;
	}

	// Get the number of steps

	int GetStepCount() { return m_Steps; }



private: // methods

	// This is called when a search fails or is canceled to free all used memory
	void FreeAllNodes()
	{
		// iterate open list and delete all nodes
		typename vector< Node * >::iterator iterOpen = m_OpenList.begin();

		while( iterOpen != m_OpenList.end() )
		{
			Node *n = (*iterOpen);
			FreeNode( n );

			iterOpen ++;
		}

		m_OpenList.clear();

		// iterate closed list and delete unused nodes
		typename vector< Node * >::iterator iterClosed;

		for( iterClosed = m_ClosedList.begin(); iterClosed != m_ClosedList.end(); iterClosed ++ )
		{
			Node *n = (*iterClosed);
			FreeNode( n );
		}

		m_ClosedList.clear();

		// delete the goal

		FreeNode(m_Goal);
	}


	// This call is made by the search class when the search ends. A lot of nodes may be
	// created that are still present when the search ends. They will be deleted by this
	// routine once the search ends
	void FreeUnusedNodes()
	{
		// iterate open list and delete unused nodes
		typename vector< Node * >::iterator iterOpen = m_OpenList.begin();

		while( iterOpen != m_OpenList.end() )
		{
			Node *n = (*iterOpen);

			if( !n->child )
			{
				FreeNode( n );

				n = NULL;
			}

			iterOpen ++;
		}

		m_OpenList.clear();

		// iterate closed list and delete unused nodes
		typename vector< Node * >::iterator iterClosed;

		for( iterClosed = m_ClosedList.begin(); iterClosed != m_ClosedList.end(); iterClosed ++ )
		{
			Node *n = (*iterClosed);

			if( !n->child )
			{
				FreeNode( n );
				n = NULL;

			}
		}

		m_ClosedList.clear();

	}

	// Node memory management
	Node *AllocateNode()
	{
		m_AllocateNodeCount ++;
		Node *p = new Node;
		return p;
	}

	void FreeNode( Node *node )
	{
		m_AllocateNodeCount --;
		delete node;
	}

private: // data

	// Heap (simple vector but used as a heap)
	vector< Node *> m_OpenList;

	// Closed list is a vector.
	vector< Node * > m_ClosedList;

	// Successors is a vector filled out by the user each time successors to a node
	// are generated
	vector< Node * > m_Successors;

	// State
	unsigned int m_State;

	// Counts steps
	int m_Steps;

	// Start and goal state pointers
	Node *m_Start;
	Node *m_Goal;

	Node *m_CurrentSolutionNode;



	//Debug : need to keep these two iterators around for the user Debug functions
	typename vector< Node * >::iterator iterDbgOpen;
	typename vector< Node * >::iterator iterDbgClosed;

	// debugging : count memory allocation and free's
	int m_AllocateNodeCount;


};


// A* Algorithm Ends ----------------------------------------------------------------------------------------------------------------------------




// Actual Program Starts ------------------------------------------------------------------------------------------------------------------------

const int MAX_CITIES = 20;

enum ENUM_CITIES{Arad=0, Bucharest, Craiova, Drobeta, Eforie, Fagaras, Giurgiu, Hirsova, Iasi, Lugoj, Mehadia, Neamt, Oradea, Pitesti, RimnicuVilcea, Sibiu, Timisoara, Urziceni, Vaslui, Zerind};
vector<string> CityNames(MAX_CITIES);
float RomaniaMap[MAX_CITIES][MAX_CITIES];

class PathSearchNode
{
public:

  ENUM_CITIES city;

	PathSearchNode() { city = Arad; }
	PathSearchNode( ENUM_CITIES in ) { city = in; }

    float GoalDistanceEstimate( PathSearchNode &nodeGoal );
	bool IsGoal( PathSearchNode &nodeGoal );
	bool GetSuccessors( AStarSearch<PathSearchNode> *astarsearch, PathSearchNode *parent_node );
	float GetCost( PathSearchNode &successor );
	bool IsSameState( PathSearchNode &rhs );

	void PrintNodeInfo();
};

// check if "this" node is the same as "RHS" node
bool PathSearchNode::IsSameState( PathSearchNode &rhs )
{
  if(city == rhs.city) return(true);
  return(false);
}

// Euclidean distance between "this" node city and Bucharest
float PathSearchNode::GoalDistanceEstimate( PathSearchNode &nodeGoal )
{
  // goal is always Bucharest!
  switch(city)
  {
    case Arad: return 366; break;
    case Bucharest: return 0; break;
    case Craiova: return 160; break;
    case Drobeta: return 242; break;
    case Eforie: return 161; break;
    case Fagaras: return 176; break;
    case Giurgiu: return 77; break;
    case Hirsova: return 151; break;
    case Iasi: return 226; break;
    case Lugoj: return 244; break;
    case Mehadia: return 241; break;
    case Neamt: return 234; break;
    case Oradea: return 380; break;
    case Pitesti: return 100; break;
    case RimnicuVilcea: return 193; break;
    case Sibiu: return 253; break;
    case Timisoara: return 329; break;
    case Urziceni: return 80; break;
    case Vaslui: return 199; break;
    case Zerind: return 374; break;
  }
  cerr << "ASSERT: city = " << CityNames[city] << endl;
	return 0;
}

// check if "this" node is the goal node
bool PathSearchNode::IsGoal( PathSearchNode &nodeGoal )
{
	if( city == Bucharest ) return(true);
	return(false);
}

// generates the successor nodes of "this" node
bool PathSearchNode::GetSuccessors( AStarSearch<PathSearchNode> *astarsearch, PathSearchNode *parent_node )
{
  PathSearchNode NewNode;
  for(int c=0; c<MAX_CITIES; c++)
  {
    if(RomaniaMap[city][c] < 0) continue;
    NewNode = PathSearchNode((ENUM_CITIES)c);
    astarsearch->AddSuccessor( NewNode );
  }
	return true;
}

// the cost of going from "this" node to the "successor" node
float PathSearchNode::GetCost( PathSearchNode &successor )
{
	return RomaniaMap[city][successor.city];
}

// prints out information about the node
void PathSearchNode::PrintNodeInfo()
{
	cout << CityNames[city];
}

int main( )
{
  // creating map of Romania
  for(int i=0; i<MAX_CITIES; i++)
    for(int j=0; j<MAX_CITIES; j++)
      RomaniaMap[i][j]=-1.0;

  RomaniaMap[Arad][Sibiu]=140;
  RomaniaMap[Arad][Zerind]=75;
  RomaniaMap[Arad][Timisoara]=118;
  RomaniaMap[Bucharest][Giurgiu]=90;
  RomaniaMap[Bucharest][Urziceni]=85;
  RomaniaMap[Bucharest][Fagaras]=211;
  RomaniaMap[Bucharest][Pitesti]=101;
  RomaniaMap[Craiova][Drobeta]=120;
  RomaniaMap[Craiova][RimnicuVilcea]=146;
  RomaniaMap[Craiova][Pitesti]=138;
  RomaniaMap[Drobeta][Craiova]=120;
  RomaniaMap[Drobeta][Mehadia]=75;
  RomaniaMap[Eforie][Hirsova]=75;
  RomaniaMap[Fagaras][Bucharest]=211;
  RomaniaMap[Fagaras][Sibiu]=99;
  RomaniaMap[Giurgiu][Bucharest]=90;
  RomaniaMap[Hirsova][Eforie]=86;
  RomaniaMap[Hirsova][Urziceni]=98;
  RomaniaMap[Iasi][Vaslui]=92;
  RomaniaMap[Iasi][Neamt]=87;
  RomaniaMap[Lugoj][Timisoara]=111;
  RomaniaMap[Lugoj][Mehadia]=70;
  RomaniaMap[Mehadia][Lugoj]=70;
  RomaniaMap[Mehadia][Drobeta]=75;
  RomaniaMap[Neamt][Iasi]=87;
  RomaniaMap[Oradea][Zerind]=71;
  RomaniaMap[Oradea][Sibiu]=151;
  RomaniaMap[Pitesti][Bucharest]=101;
  RomaniaMap[Pitesti][RimnicuVilcea]=97;
  RomaniaMap[Pitesti][Craiova]=138;
  RomaniaMap[RimnicuVilcea][Pitesti]=97;
  RomaniaMap[RimnicuVilcea][Craiova]=146;
  RomaniaMap[RimnicuVilcea][Sibiu]=80;
  RomaniaMap[Sibiu][RimnicuVilcea]=80;
  RomaniaMap[Sibiu][Fagaras]=99;
  RomaniaMap[Sibiu][Oradea]=151;
  RomaniaMap[Sibiu][Arad]=140;
  RomaniaMap[Timisoara][Arad]=118;
  RomaniaMap[Timisoara][Lugoj]=111;
  RomaniaMap[Urziceni][Bucharest]=85;
  RomaniaMap[Urziceni][Hirsova]=98;
  RomaniaMap[Urziceni][Vaslui]=142;
  RomaniaMap[Vaslui][Urziceni]=142;
  RomaniaMap[Vaslui][Iasi]=92;
  RomaniaMap[Zerind][Arad]=75;
  RomaniaMap[Zerind][Oradea]=71;

  // City names
  CityNames[Arad].assign("Arad");
  CityNames[Bucharest].assign("Bucharest");
  CityNames[Craiova].assign("Craiova");
  CityNames[Drobeta].assign("Drobeta");
  CityNames[Eforie].assign("Eforie");
  CityNames[Fagaras].assign("Fagaras");
  CityNames[Giurgiu].assign("Giurgiu");
  CityNames[Hirsova].assign("Hirsova");
  CityNames[Iasi].assign("Iasi");
  CityNames[Lugoj].assign("Lugoj");
  CityNames[Mehadia].assign("Mehadia");
  CityNames[Neamt].assign("Neamt");
  CityNames[Oradea].assign("Oradea");
  CityNames[Pitesti].assign("Pitesti");
  CityNames[RimnicuVilcea].assign("RimnicuVilcea");
  CityNames[Sibiu].assign("Sibiu");
  CityNames[Timisoara].assign("Timisoara");
  CityNames[Urziceni].assign("Urziceni");
  CityNames[Vaslui].assign("Vaslui");
  CityNames[Zerind].assign("Zerind");

  ENUM_CITIES initCity = Arad; // Choose your start state.

    // An instance of A* search class
	AStarSearch<PathSearchNode> astarsearch;

	unsigned int SearchCount = 0;
	const unsigned int NumSearches = 1;

	while(SearchCount < NumSearches)
	{
		// Create a start state
		PathSearchNode nodeStart;
		nodeStart.city = initCity;

		// Define the goal state, always Bucharest!
		PathSearchNode nodeEnd;
		nodeEnd.city = Bucharest;

		// Set Start and goal states
		astarsearch.SetStartAndGoalStates( nodeStart, nodeEnd );

		unsigned int SearchState;
		unsigned int SearchSteps = 0;

		do
		{

			SearchSteps++;
            cout << "Step " << SearchSteps << ": ";
            SearchState = astarsearch.SearchStep();

			int len = 0;

			cout << "Open List:\n";
			PathSearchNode *p = astarsearch.GetOpenListStart();
			if(p==NULL)
                cout << "\tEmpty\n";
            while( p )
			{
				len++;

				cout<<"\t";
				((PathSearchNode *)p)->PrintNodeInfo();
				cout<<"\n";

				p = astarsearch.GetOpenListNext();

			}
			cout << "\nOpen list has " << len << " nodes\n";

			len = 0;

			cout << "\nClosed List:\n";
			p = astarsearch.GetClosedListStart();
			if(p==NULL)
                cout << "\tEmpty\n";
			while(p)
			{
				len++;

				cout<<"\t";
				p->PrintNodeInfo();
				cout<<"\n";
				p = astarsearch.GetClosedListNext();
			}

			cout << "\nClosed list has " << len << " nodes\n\n---------------------------------------------\n\n";



		}
		while( SearchState == AStarSearch<PathSearchNode>::SEARCH_STATE_SEARCHING );

		if( SearchState == AStarSearch<PathSearchNode>::SEARCH_STATE_SUCCEEDED )
		{
			cout << "Search found the goal state.\n\n";
      PathSearchNode *node = astarsearch.GetSolutionStart();
      cout << "Displaying solution...\n\n";
      int steps = 0;
      node->PrintNodeInfo();
      for( ;; )
      {
        node = astarsearch.GetSolutionNext();
        if( !node ) break;
        cout<< " -> ";
        node->PrintNodeInfo();
        steps ++;
      };
      cout << "\n\nSolution steps:  " << steps << endl;
      // Once we're done with the solution we can free the nodes up
			astarsearch.FreeSolutionNodes();
		}
		else if( SearchState == AStarSearch<PathSearchNode>::SEARCH_STATE_FAILED )
		{
			cout << "Search terminated. Did not find goal state\n";
		}
		// Display the number of loops the search went through
		cout << "SearchSteps : " << SearchSteps << "\n";
		SearchCount ++;

	}

	return 0;
}
