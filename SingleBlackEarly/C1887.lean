import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1887 : checkSingleBlackFast (-65, -37) 25009 .east (28, 16) (6, -51) = true := by
  decide +kernel

end LangtonsAnt
