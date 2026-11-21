import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1737 : checkSingleBlackFast (-50, -27) 13847 .west (12, 22) (-41, 2) = true := by
  decide +kernel

end LangtonsAnt
