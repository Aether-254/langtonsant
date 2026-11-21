import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1644 : checkSingleBlackFast (-43, -16) 26912 .north (5, 17) (-17, -39) = true := by
  decide +kernel

end LangtonsAnt
