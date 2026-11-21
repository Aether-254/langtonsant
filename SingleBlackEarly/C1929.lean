import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1929 : checkSingleBlackFast (-68, -42) 13044 .north (23, 15) (-49, -31) = true := by
  decide +kernel

end LangtonsAnt
