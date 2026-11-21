import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1811 : checkSingleBlackFast (-54, -35) 20608 .north (29, 25) (-55, -17) = true := by
  decide +kernel

end LangtonsAnt
