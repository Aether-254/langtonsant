import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1687 : checkSingleBlackFast (-46, -20) 11900 .north (12, 4) (-38, -20) = true := by
  decide +kernel

end LangtonsAnt
