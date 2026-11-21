import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0724 : checkSingleBlackFast2 (6, -13) 10460 .north (-3, -2) (-27, 0) = true := by
  decide +kernel

end LangtonsAnt
