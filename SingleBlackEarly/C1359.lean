import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1359 : checkSingleBlackFast (-14, 5) 21908 .north (6, -13) (-32, 3) = true := by
  decide +kernel

end LangtonsAnt
