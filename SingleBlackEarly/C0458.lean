import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0458 : checkSingleBlackFast (18, 11) 6976 .north (-10, 7) (0, -17) = true := by
  decide +kernel

end LangtonsAnt
