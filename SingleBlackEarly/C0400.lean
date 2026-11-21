import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0400 : checkSingleBlackFast (13, -7) 27258 .north (-7, 10) (-34, -17) = true := by
  decide +kernel

end LangtonsAnt
