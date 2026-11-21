import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1969 : checkSingleBlackFast (-67, -49) 12944 .north (23, 15) (-49, -31) = true := by
  decide +kernel

end LangtonsAnt
