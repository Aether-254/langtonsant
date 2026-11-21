import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1623 : checkSingleBlackFast (-41, -13) 26513 .east (9, -11) (-33, -6) = true := by
  decide +kernel

end LangtonsAnt
