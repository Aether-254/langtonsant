import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0590 : checkSingleBlackFast (19, 13) 6996 .north (-10, 7) (0, -17) = true := by
  decide +kernel

end LangtonsAnt
