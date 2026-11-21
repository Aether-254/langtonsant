import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1847 : checkSingleBlackFast (-60, -37) 14367 .west (17, 27) (-46, 7) = true := by
  decide +kernel

end LangtonsAnt
