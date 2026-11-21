import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2186 : checkSingleBlackFast (-88, -70) 30019 .east (47, 35) (6, -57) = true := by
  decide +kernel

end LangtonsAnt
