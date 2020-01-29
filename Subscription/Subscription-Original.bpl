// Subscription Application

type Pid;
type Uid;

function {:builtin "MapConst"} MapConstBool(bool) : [Pid]bool;
function {:inline} {:linear "pid"} TidCollector(x: Pid) : [Pid]bool
{
  MapConstBool(false)[x := true]
}

function {:builtin "MapConst"} MapConstBool2(bool) : [Uid]bool;
function {:inline} {:linear "uid"} TidCollector2(x: Uid) : [Uid]bool
{
  MapConstBool2(false)[x := true]
}

var {:layer 0,2} ActiveUser: [Uid]bool;
var {:layer 0,2} UserPassword: [Uid]int;


procedure {:atomic}{:layer 2}  addUser(uid:Uid, p: int)
modifies ActiveUser, UserPassword;
{  
    assume (!ActiveUser[uid] && UserPassword[uid] == 0 && p != 0);
    
	ActiveUser[uid] := true; 
    UserPassword[uid] := p;
}
procedure{:yields}{:layer 1} {:refines "addUser"} AddUser(uid:Uid, p: int);
ensures {:layer 1} ( (!old(ActiveUser[uid]) && UserPassword[uid] == 0 && p != 0) ==> (ActiveUser[uid] && UserPassword[uid] == p) );


procedure {:atomic}{:layer 2}  removeUser({:linear "uid"} uid:Uid)
modifies ActiveUser, UserPassword;
{  
    assume (ActiveUser[uid] && UserPassword[uid] != 0);
    
	ActiveUser[uid] := false; 
    UserPassword[uid] := -1;
}
procedure{:yields}{:layer 1} {:refines "removeUser"} RemoveUser({:linear "uid"} uid:Uid);
ensures {:layer 1} ( (old(ActiveUser[uid]) && old(UserPassword[uid]) != 0) ==> (!ActiveUser[uid] && UserPassword[uid] == -1) );
