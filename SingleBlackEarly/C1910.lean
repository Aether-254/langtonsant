import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1910 : checkSingleBlackFast (-65, -40) 21167 .east (35, 14) (-11, -53) = true := by
  decide +kernel

end LangtonsAnt
