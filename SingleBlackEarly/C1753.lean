import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1753 : checkSingleBlackFast (-52, -26) 12212 .north (15, 7) (-41, -23) = true := by
  decide +kernel

end LangtonsAnt
