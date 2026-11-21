import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1201 : checkSingleBlackFast (24, 5) 11524 .north (-3, 0) (-27, 2) = true := by
  decide +kernel

end LangtonsAnt
