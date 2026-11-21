import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1219 : checkSingleBlackFast (22, 11) 13072 .north (-3, 0) (-27, 2) = true := by
  decide +kernel

end LangtonsAnt
