import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0769 : checkSingleBlackFast (20, -17) 10608 .north (0, 1) (-24, 3) = true := by
  decide +kernel

end LangtonsAnt
