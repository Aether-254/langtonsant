import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2063 : checkSingleBlackFast (-81, -53) 25841 .east (36, 24) (14, -59) = true := by
  decide +kernel

end LangtonsAnt
