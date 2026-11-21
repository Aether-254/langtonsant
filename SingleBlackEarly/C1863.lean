import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1863 : checkSingleBlackFast (-62, -36) 12732 .north (20, 12) (-46, -28) = true := by
  decide +kernel

end LangtonsAnt
